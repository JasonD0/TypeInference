module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)
{-
data Type = Arrow Type Type
          | Prod Type Type
          | Sum Type Type
          | Base BaseType
          | TypeVar Id
-}
unify :: Type -> Type -> TC Subst
-- both type variables
unify (TypeVar v1) (TypeVar v2) | v1 == v2  = return emptySubst
                                | otherwise = return (v1 =: TypeVar v2)

-- both primitive types
unify (Base b1) (Base b2) | b1 == b2  = return emptySubst
                          | otherwise = typeError (TypeMismatch (Base b1) (Base b2))

-- both product types 
unify (Prod t11 t12) (Prod t21 t22) = do s  <- unify t11 t21
                                         s' <- unify (substitute s t12) (substitute s t22)
                                         return (s<>s')

-- both sum types 
unify (Sum t11 t12) (Sum t21 t22) = do s  <- unify t11 t21 
                                       s' <- unify (substitute s t12) (substitute s t22) 
                                       return (s<>s')

-- both func types 
unify (Arrow t11 t12) (Arrow t21 t22) = do s  <- unify t11 t21
                                           s' <- unify (substitute s t12) (substitute s t22)
                                           return (s<>s')

-- type variable and term t 
unify (TypeVar v) t | elem v (tv t) = typeError (OccursCheckFailed v t)
                    | otherwise = return (v =: t)
unify t (TypeVar v) | elem v (tv t) = typeError (OccursCheckFailed v t)
                    | otherwise = return (v =: t)

-- no unifier
unify t1 t2 = typeError (TypeMismatch t1 t2)

generalise :: Gamma -> Type -> QType
generalist g t = generalise' ((tv t) \\ (tvGamma g)) t
generalise g t = error "implement me"

generalise' :: [Id] -> Type -> QType
generalise' [] t = Ty t
generalise' (ident:idents) t = Forall ident (generalise' idents t)

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env [(Bind main types args e)] = do  (e', t, sub) <- inferExp env e 
                                                  return ([allTypesBind (substQType sub) (Bind main (Just (generalise env t)) args e')], t, sub)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
-- Constants and Variables
inferExp g (Num n) = return (Num n, Base Int, emptySubst)
inferExp g (Var x) = case E.lookup g x of 
                        (Just v)  -> do v' <- unquantify v 
                                        return (Var x, v', emptySubst)  
                        (Nothing) -> typeError (NoSuchVariable x)

-- Constructors and Primops
inferExp g (Con id) = case constType id of 
                        (Just c)  -> do c' <- unquantify c 
                                        return (Con id, c', emptySubst)
                        (Nothing) -> typeError (NoSuchConstructor id)

inferExp g (Prim o) = do p <- unquantify (primOpType o) 
                         return (Prim o, p, emptySubst)

-- Application
inferExp g (App e1 e2) = do (e1', t1, sub)    <- inferExp g e1 
                            (e2', t2, sub')   <- inferExp (substGamma sub g) e2
                            alpha             <- fresh
                            u                 <- unify (substitute sub' t1) (Arrow t2 alpha)
                            return (App e1' e2', substitute u alpha, u<>sub'<>sub) 

-- If-Then-Else
inferExp g (If e e1 e2) = do  (e', t, sub)     <- inferExp g e 
                              u                <- unify t (Base Bool)
                              (e1', t1, sub')  <- inferExp (substGamma (u<>sub) g) e1
                              (e2', t2, sub'') <- inferExp (substGamma (sub'<>u<>sub) g) e2
                              u'               <- unify (substitute sub'' t1) t2
                              return (If e' e1' e2', substitute u' t2, u'<>sub''<>sub'<>u<>sub) 

-- Case
-- -- Note: this is the only case you need to handle for case expressions
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do (e', t, sub)     <- inferExp g e
                                                              alphal           <- fresh 
                                                              alphar           <- fresh
                                                              (e1', tl, sub')  <- inferExp (substGamma sub (E.add g (x, Ty alphal))) e1
                                                              (e2', tr, sub'') <- inferExp (substGamma (sub'<>sub) (E.add g (y, Ty alphar))) e2
                                                              u                <- unify (substitute (sub''<>sub'<>sub) (Sum alphal alphar)) (substitute (sub''<>sub') t)
                                                              u'               <- unify (substitute (u<>sub'') tl) (substitute u tr)
                                                              return ((Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2']), substitute u' (substitute u tr), u'<>u<>sub''<>sub'<>sub)
inferExp g (Case e _) = typeError MalformedAlternatives

-- Recursive Functions    --Bind Id (Maybe QType) [Id] Exp
inferExp g (Recfun (Bind f _ [x] e)) = do alpha1       <- fresh
                                          alpha2       <- fresh
                                          (e', t, sub) <- inferExp (E.addAll g [(x, Ty alpha1), (f, Ty alpha2)]) e 
                                          u            <- unify (substitute sub alpha2) (Arrow (substitute sub alpha1) t)
                                          return (Recfun (Bind f (Just (Ty (substitute u (Arrow (substitute sub alpha1) t)))) [x] e'), substitute u (Arrow (substitute sub alpha1) t), u<>sub)

-- Let Bindings
inferExp g (Let bs e) = do  (bs', g', sub) <- inferBindings g bs 
                            (e', t, sub')  <- inferExp g' e
                            return (Let bs' e', t, sub'<>sub)

-- Go through all let bindings
inferBindings :: Gamma -> [Bind] -> TC ([Bind], Gamma, Subst) 
inferBindings g [(Bind x types idents e)] = do (e', t, sub)   <- inferExp g e
                                               return ([(Bind x (Just (generalise (substGamma sub g) t)) idents e')], E.add (substGamma sub g) (x, generalise (substGamma sub g) t), sub)
inferBindings g ((Bind x types idents e):bs) = do (e', t, sub)    <- inferExp g e 
                                                  (bs', g', sub') <- inferBindings (E.add (substGamma sub g) (x, generalise (substGamma sub g) t)) bs 
                                                  return ((Bind x (Just (generalise g' t)) idents e'):bs', g', sub'<>sub)