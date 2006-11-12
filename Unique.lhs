The Unique module implements the Normal Form function by
using Barendregt's variable convention, i.e., all bound
variables are unique.

> module Unique(nf) where
> import Lambda
> import qualified Data.Map as M
> import Control.Monad.State
> import IdInt

The first step is to make all variables unique.
Then normal form is computed by repeatedly performing
substitution (beta reduction) on the leftmost redex.
Normalization is run in a State monad with the next free variable.


> nf :: LC IdInt -> LC IdInt
> nf e = evalState (nf' e') i
>   where (e', (i, _)) = runState (unique e) (firstBoundId, M.empty)

> type N a = State IdInt a

> nf' :: LC IdInt -> N (LC IdInt)
> nf' e@(Var _) = return e
> nf' (Lam x e) = liftM (Lam x) (nf' e)
> nf' (App f a) = do
>     f' <- whnf f
>     case f' of
>         Lam x b -> subst x a b >>= nf'
>         _ -> liftM2 App (nf' f') (nf' a)

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
> subst x s b = sub b
>  where sub e@(Var v) | v == x = clone M.empty s
>                      | otherwise = return e
>        sub (Lam v e) = liftM (Lam v) (sub e)
>        sub (App f a) = liftM2 App (sub f) (sub a)
>
>        clone m e@(Var v) = return $ maybe e Var (M.lookup v m)
>        clone m (Lam v e) = do v' <- newVar; liftM (Lam v') (clone (M.insert v v' m) e)
>        clone m (App f a) = liftM2 App (clone m f) (clone m a)

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

> type U a = State (IdInt, M.Map IdInt IdInt) a

> unique :: LC IdInt -> U (LC IdInt)
> unique (Var v) = liftM Var (getVar v)
> unique (Lam v e) = liftM2 Lam (addVar v) (unique e)
> unique (App f a) = liftM2 App (unique f) (unique a)

Add a variable to the mapping.

> addVar :: IdInt -> U IdInt
> addVar v = do
>    (i, m) <- get
>    put (succ i, M.insert v i m)
>    return i

Find an existing variable in the mapping.

> getVar :: IdInt -> U IdInt
> getVar v = do
>     (_, m) <- get
>     return $ maybe v id (M.lookup v m)
