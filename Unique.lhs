The Unique module implements the Normal Form function by
using Barendregt's variable convention, i.e., all bound
variables are unique.

> module Unique(nf,Unique.aeq, toUnique) where
> import Lambda as LC
> import qualified Data.Map as M
> import Control.Monad.State
> import IdInt
> import Data.Maybe (fromMaybe)
> import Debug.Trace

The first step is to make all variables unique.
Then normal form is computed by repeatedly performing
substitution (beta reduction) on the leftmost redex.
Normalization is run in a State monad with the next free variable.

> nf :: LC IdInt -> LC IdInt
> nf e = evalState (nf' e') i
>   where (e', i) = runState (unique M.empty e) (initState e)

Note: we don't want to capture any free variables, so we need to start our
conversion function with the maxium FV in the term.

> initState :: LC IdInt -> IdInt
> initState e = succ x where
>      vs = LC.freeVars e
>      x  = case vs of [] -> firstBoundId ; _ -> max firstBoundId (maximum vs)



> toUnique :: LC IdInt -> LC IdInt
> toUnique e = e'
>   where
>      (e', _) = runState (unique M.empty e) (initState e)

> type N a = State IdInt a

> nf' :: LC IdInt -> N (LC IdInt)
> nf' e@(Var _) = return e
> nf' (Lam x e) = liftM (Lam x) (nf' e)
> nf' (App f a) = do
>     f' <- whnf f
>     case f' of
>         Lam x b -> subst x a b >>= nf'
>         _ -> App <$> nf' f' <*> nf' a

Compute the weak head normal form.

> whnf :: LC IdInt -> N (LC IdInt)
> whnf e@(Var _) = return e
> whnf e@(Lam _ _) = return e
> whnf (App f a) = do
>     f' <- whnf f
>     case f' of
>         Lam x b -> subst x a b >>= whnf
>         _ -> return $ App f' a

Substitution proceeds by cloning the term that is inserted
at every place it is put.

(TODO: No need to clone $\lambda$-free terms.)

> subst :: IdInt -> LC IdInt -> LC IdInt -> N (LC IdInt)
> subst x s = sub
>  where sub e@(Var v) | v == x = clone M.empty s
>                      | otherwise = return e
>        sub (Lam v e) = liftM (Lam v) (sub e)
>        sub (App f a) = liftM2 App (sub f) (sub a)
>
>        clone m e@(Var v) = return $ maybe e Var (M.lookup v m)
>        clone m (Lam v e) = do v' <- newVar; liftM (Lam v') (clone (M.insert v v' m) e)
>        clone m (App f a) = liftM2 App (clone m f) (clone m a)
>


Create a fresh variable.

> newVar :: N IdInt
> newVar = do
>     i <- get
>     put (succ i)
>     return i

Do the actual translation of the term to unique variables.
We keep mapping of old variable names to new variable name.
Free variables are just left alone since they are already
uniquely named.

> type U a  = State IdInt a
> type Env  = M.Map IdInt IdInt

> unique :: Env -> LC IdInt -> U (LC IdInt)
> unique env (Var v)   = return $ Var (getVar env v)
> unique env (Lam v e) = do
>    (i, env') <- addVar env v
>    Lam i <$> unique env' e
> unique env (App f a) = App <$> unique env f <*> unique env a

Add a variable to the mapping.

> addVar :: Env -> IdInt -> U (IdInt,Env)
> addVar env v = do
>    i <- get
>    put (succ i)
>    return (i,M.insert v i env)


Find an existing variable in the mapping.

> getVar :: Env -> IdInt -> IdInt
> getVar m v = fromMaybe v (M.lookup v m)

Alpha-equivalence: generate a fresh name for each binding variable.

> type Env2 = (M.Map IdInt IdInt, M.Map IdInt IdInt)
>
> getVar2 :: Env2 -> IdInt -> IdInt -> (IdInt,IdInt)
> getVar2 (m1,m2) v1 v2 = do
>     (fromMaybe v1 (M.lookup v1 m1), fromMaybe v2 (M.lookup v2 m2))

> addVar2 :: Env2 -> IdInt -> IdInt -> U Env2
> addVar2 (m1,m2) v1 v2 = do
>    i <- get
>    put (succ i)
>    return (M.insert v1 i m1, M.insert v2 i m2)


> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq a b = evalState (uaeq (M.empty,M.empty) a b) firstBoundId

> uaeq ::  Env2 -> LC IdInt -> LC IdInt -> U Bool
> uaeq env (Var v1) (Var v2)       = do
>     let (v1', v2') = getVar2 env v1 v2
>     return $ v1' == v2'
> uaeq env (Lam v1 e1) (Lam v2 e2) = do
>     env' <- addVar2 env v1 v2
>     uaeq env' e1 e2
> uaeq env (App a1 a2) (App b1 b2) = liftM2 (&&) (uaeq env a1 b1) (uaeq env a2 b2)
> uaeq _env u1 u2 = do
>   traceM $ "Cannot match " ++ show u1 ++ " and " ++ show u2
>   return False
