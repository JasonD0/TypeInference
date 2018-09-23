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

unify :: Type -> Type -> TC Subst
unify = error "implement me"

generalise :: Gamma -> Type -> QType
generalise g t = error "implement me"

inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"

{-
data Exp              data Type = Arrow Type Type
    = Var Id                    | Prod Type Type
    | Prim Op                   | Sum Type Type
    | Con Id                    | Base BaseType
    | Num Integer               | TypeVar Id
    | App Exp Exp
    | If Exp Exp Exp
    | Let [Bind] Exp
    | Recfun Bind
    | Letrec [Bind] Exp
    | Case Exp [Alt]


data TypeError = TypeMismatch Type Type
               | OccursCheckFailed Id Type
               | NoSuchVariable Id
               | NoSuchConstructor Id
               | MalformedAlternatives
               | ForallInRecfun
-}

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
                              return (If e' e1' e2', substitute U' t2, U'<>U<>T''<>T'<>T) 

-- Case
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives

-- Recursive Functions

-- Let Bindings



