The Unique module implements the Normal Form function by
using Barendregt's variable convention, i.e., all bound
variables are unique.

> {-# LANGUAGE PatternSynonyms #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> module Unique(nf, Unique.aeq, toUnique, fromUnique, impl, Unique) where
> import Lambda as LC
> import qualified Data.Map as M
> import Control.Monad.State
> import IdInt
> import Data.Maybe (fromMaybe)
> import Data.Coerce
> import Control.DeepSeq
> 
> import Test.QuickCheck

The first step is to make all variables unique.
Then normal form is computed by repeatedly performing
substitution (beta reduction) on the leftmost redex.
Normalization is run in a State monad with the next free variable.

> import Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "Unique"
>           , impl_fromLC = toUnique
>           , impl_toLC   = fromUnique
>           , impl_nf     = nfd
>           , impl_nfi    = error "nfi not implemented for Unique"
>           , impl_aeq    = (==)
>        }



> nf :: LC IdInt -> LC IdInt
> nf e = fromUnique $ evalState (nf' e') i
>   where (e', i) = freshen e

> newtype Unique = MkU { fromUnique :: LC IdInt } deriving (Eq, Show, NFData)

> pattern UVar x     <- MkU (Var x)
> pattern UApp e1 e2 <- MkU (App e1 e2)
> pattern ULam x e   <- MkU (Lam x e)

> uvar :: IdInt -> Unique
> uvar = coerce (Var @IdInt)
> ulam :: IdInt -> Unique -> Unique
> ulam = coerce (Lam @IdInt)
> uapp :: Unique -> Unique -> Unique
> uapp = coerce (App @IdInt)
 


Note: we don't want to capture any free variables, so we need to start our
conversion function with the maxium FV in the term.

> initState :: LC IdInt -> IdInt
> initState e = succ x where
>      vs = LC.freeVars e
>      x  = case vs of [] -> firstBoundId ; _ -> max firstBoundId (maximum vs)

> freshen :: LC IdInt -> (Unique, IdInt)
> freshen e = runState (unique M.empty e) (initState e)

> toUnique :: LC IdInt -> Unique
> toUnique e = fst (freshen e)

Our state monad. 

> type N a = State IdInt a

> nfd :: Unique -> Unique
> nfd e = evalState (nf' e) (initState (fromUnique e))

> nf' :: Unique -> N Unique
> nf' e@(UVar _) = return e
> nf' (ULam x e) = ulam x <$> nf' (MkU e)
> nf' (UApp f a) = do
>     f' <- whnf (MkU f)
>     case f' of
>         ULam x b -> subst x (MkU a) (MkU b) >>= nf'
>         _ -> uapp <$> nf' f' <*> nf' (MkU a)

Compute the weak head normal form.

> whnf :: Unique -> N Unique
> whnf e@(UVar _) = return e
> whnf e@(ULam _ _) = return e
> whnf (UApp f a) = do
>     f' <- whnf (MkU f)
>     case f' of
>         ULam x b -> subst x (MkU a) (MkU b) >>= whnf
>         _ -> return $ uapp f' (MkU a)

Fueled version:

<< TODO >>



Substitution proceeds by cloning the term that is inserted
at every place it is put.

(TODO: No need to clone $\lambda$-free terms.)

> subst :: IdInt -> Unique -> Unique -> N Unique
> subst x s = sub
>  where sub :: Unique -> N Unique
>        sub e@(UVar v) | v == x    = clone M.empty s
>                       | otherwise = return e
>        sub (ULam v e) = ulam v <$> sub (MkU e)
>        sub (UApp f a) = uapp <$> sub (MkU f) <*> sub (MkU a)
>
> --       clone m e@(Var v) = return $ maybe e Var (M.lookup v m)
> --       clone m (Lam v e) = do v' <- newVar; liftM (Lam v') (clone (M.insert v v' m) e)
> --       clone m (App f a) = liftM2 App (clone m f) (clone m a)
>

> clone :: Env -> Unique -> U Unique
> clone = coerce unique

Create a fresh variable.

> -- newVar :: N IdInt
> -- newVar = do
> --    i <- get
> --    put (succ i)
> --    return i

Do the actual translation of the term to unique variables.
We keep mapping of old variable names to new variable name.
Free variables are just left alone since they are already
uniquely named.

> type U a  = State IdInt a
> type Env  = M.Map IdInt IdInt

> unique :: Env -> LC IdInt -> U Unique
> unique env (Var v)   = return $ MkU $ Var (getVar env v)
> unique env (Lam v e) = do
>    (i, env') <- addVar env v
>    ulam i <$> unique env' e
> unique env (App f a) = uapp <$> unique env f <*> unique env a

Add a variable to the mapping.

> addVar :: Env -> IdInt -> U (IdInt,Env)
> addVar env v = do
>    i <- get
>    put (succ i)
>    return (i, M.insert v i env)

Find an existing variable in the mapping.

> getVar :: Env -> IdInt -> IdInt
> getVar m v = fromMaybe v (M.lookup v m)


"Unique variable" based alpha-equivalence: generate a fresh name for each
 binding variable.

> type Env2 = (M.Map IdInt IdInt, M.Map IdInt IdInt)
>

> addVar2 :: Env2 -> IdInt -> IdInt -> U Env2
> addVar2 (m1,m2) v1 v2 = do
>    i <- get
>    put (succ i)
>    return (M.insert v1 i m1, M.insert v2 i m2)
> getVar2 :: Env2 -> IdInt -> IdInt -> (IdInt,IdInt)
> getVar2 (m1,m2) v1 v2 = do
>     (fromMaybe v1 (M.lookup v1 m1), fromMaybe v2 (M.lookup v2 m2))


> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq a b = evalState (uaeq (M.empty,M.empty) a b) (initState (App a b))

> uaeq :: Env2 -> LC IdInt -> LC IdInt -> U Bool
> uaeq env (Var v1) (Var v2)       = do
>     let (v1', v2') = getVar2 env v1 v2
>     return $ v1' == v2'
> uaeq env (Lam v1 e1) (Lam v2 e2) = do
>     env' <- addVar2 env v1 v2
>     uaeq env' e1 e2
> uaeq env (App a1 a2) (App b1 b2) = liftM2 (&&) (uaeq env a1 b1) (uaeq env a2 b2)
> uaeq _env _u1 _u2 = return False


> prop_unique :: LC IdInt -> Bool
> prop_unique x = Unique.aeq x (Unique.fromUnique (Unique.toUnique x))
