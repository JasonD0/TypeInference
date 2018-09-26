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
unify (Prod t11 t12) (Prod t21 t22) = do S  <- unify t11 t21
                                         S' <- unify (substitute S t12) (substitute S t22)
                                         return S<>S'

-- both sum types 
unify (Sum t11 t12) (Sum t21 t22) = do S  <- unify t11 t21 
                                       S' <- unify (substitute S t12) (substitute S t22) 
                                       return S<>S'

-- both func types 
unify (Arrow t11 t12) (Arrow t21 t22) = do S  <- unify t11 t21
                                           S' <- unify (substitute S t12) (substitute t22)
                                           return S<>S'

-- type variable and term t 
unify (TypeVar v) t | elem v (tv t) = typeError (OccursCheckFailed v t)
                    | otherwise return (v =: t)
unify t (TypeVar v) | elem v (tv t) = typeError (OccursCheckFailed v t)
                    | otherwise return (v =: t)

-- no unifier
unify t1 t2 = typeError (TypeMismatch t1 t2)

generalise :: Gamma -> Type -> QType
generalist g t = generalise' ((tv t) \\ (tvGamma g)) t
generalise g t = error "implement me"

generalise' :: [Id] -> QType
generalise' [] t = Ty t;
generalise' (ident:idents) t = Forall ident (generalise' idents t)

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env (Bind Main types args e) = do (e', t, T) <- inferExp env e 
                                                return ([allTypesBind (substQType T) (Bind Main (Just (generalise g t) args e'))], t, T)
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
inferExp g (Con C) = case constType C of 
                        (Just c)  -> do c' <- unquantify c 
                                        return (Con C, c', emptySubst)
                        (Nothing) -> typeError (NoSuchConstructor C)

inferExp g (Prim o) = do p <- unquantify (Prim o) 
                        return (Prim o, p, emptySubst)

-- Application
inferExp g (App e1 e2) = do (e1', t1, T)    <- inferExp g e1 
                            (e2', t2, T')   <- inferExp (substGamma T g) e2
                            alpha           <- fresh
                            U               <- unify (substitute T' t1) (Arrow t2 alpha)
                            return (App e1' e2', substitute U alpha, U<>T'<>T) 

-- If-Then-Else
inferExp g (If e e1 e2) = do (e', t, T)     <- inferExp g e 
                              U             <- unify T (Base Bool)
                              (e1', t1, T')  <- inferExp (substGamma U<>T g) e1
                              (e2', t2, T'') <- inferExp (substGamma T'<>U<>T g) e2
                              U'            <- unify (substitute T'' t1) t2
                              return (If e' e1' e2', substitute U' t2, U'<>T''<>T'<>U<>T) 

-- Case
-- -- Note: this is the only case you need to handle for case expressions
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do (e', t, T)     <- inferExp g e
                                                              alphal         <- fresh 
                                                              alphar         <- fresh
                                                              (e1', tl, T')  <- inferExp (substGamma T (E.add g (x, Ty alphal))) e1
                                                              (e2', tr, T'') <- inferExp (substGamme (T'<>T) (E.add g (y, Ty alphar))) e2
                                                              U              <- unify (substitute (T''<>T'<>T) (Sum alphal alphar)) (substitute (T''<>T') t)
                                                              U'             <- unify (substitute (U<>T'') t1) (substitute U tr)
                                                              return ((Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2']), substitute U' (substitute U tr), U'<>U<>T''<>T'<>T)
inferExp g (Case e _) = typeError MalformedAlternatives

-- Recursive Functions    --Bind Id (Maybe QType) [Id] Exp
inferExp g (Recfun (Bind f _ [x] e)) = do alpha1     <- fresh
                                          alpha2     <- fresh
                                          (e', t, T) <- inferExp (E.addAll g [(x, Ty alpha1), (f, Ty alpha2)) e 
                                          U          <- unify (substitute T alpha2) (Arrow (substitute T alpha1) t)
                                          return (Recfun (Bind f (Just (Ty (substitute U (Arrow (substitute T alpha1) t)))) [x] e'), substitute U (Arrow (substitute alpha1 t)), U<>T)

-- Let Bindings
inferExp g (Let bs e1) = do (bs', g', T) <- inferBindings g bs 
                            (e', t, T')  <- inferExp g' e 
                            return (Let bs' e', t, T'<>T)

-- Go through all let bindings
inferBingings :: Gamma -> [Bind] -> TC ([Bind], Gamma, Subst) 
inferBindings g [(Bind x types idents e)] = do (e', t, T)   <- inferExp g e
                                               return ((Bind x (Just (generalise (substGamma T g) t)) idents e'), E.add (substGamma T g) (x, generalise (substGamma T g) t), T)
inferBindings g [(Bind x types idents e):bs] = do (e', t, T)    <- inferExp g e 
                                                  (bs', g', T') <- inferBindings (E.add (substGamma T g) (x, generalise (substGamma T g) t)) bs 
                                                  return ((Bind x (Just (generalise g' t)) idents e') ++ bs', g', T'<>T)