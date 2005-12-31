The Unique module implements the Normal Form function by
using Barendregt's variable convention, i.e., all bound
variables are unique.

> module Unique(nf) where
> import Lambda
> import qualified Data.Map as M
> import Control.Monad.State
> import IdInt

> type SId = IdInt

The first step is to make all variables unique.
Then normal form is computed by repeatedly performing
substitution (beta reduction) on the leftmost redex.
Normalization is run in a State monad with the next free variable.


> nf :: LC SId -> LC SId
> nf e = evalState (nf' e') i
>   where (e', (i, _)) = runState (unique e) (0, M.empty)

> type N a = State Int a

> nf' :: LC SId -> N (LC SId)
> nf' e@(Var _) = return e
> nf' (Lam x e) = liftM (Lam x) (nf' e)
> nf' (App f a) = do
>     f' <- whnf f
>     case f' of
>         Lam x b -> subst x a b >>= nf'
>         _ -> liftM2 App (nf' f') (nf' a)

Compute the weak head normal form.

> whnf :: LC SId -> N (LC SId)
> whnf e@(Var _) = return e
> whnf e@(Lam _ _) = return e
> whnf (App f a) = do
>     f' <- whnf f
>     case f' of
>         Lam x b -> subst x a b >>= whnf
>         _ -> return $ App f' a

Substitution proceeds by cloning the term that is inserted
at every place it is put.
XXX No need to clone lambda free terms.

> subst :: SId -> LC SId -> LC SId -> N (LC SId)
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

> newVar :: N SId
> newVar = do
>     i <- get
>     put (i+1)
>     return $ IdInt i

To make all variables unique we first find the free variables
and add them to the translation map, then we convert the term
using a new variable for each lambda.

> type U a = State (Int, M.Map SId SId) a

> unique :: LC SId -> U (LC SId)
> unique e = do
>     mapM_ addVar (freeVars e)
>     uniq e

Do the actual translation of the term to unique variables.

> uniq :: LC SId -> U (LC SId)
> uniq (Var v) = liftM Var (getVar v)
> uniq (Lam v e) = liftM2 Lam (addVar v) (uniq e)
> uniq (App f a) = liftM2 App (uniq f) (uniq a)

Add a variable to the mapping.

> addVar :: SId -> U SId
> addVar v = do
>    (i, m) <- get
>    let ii = IdInt i
>    put (i+1, M.insert v ii m)
>    return ii

Find an existing variable in the mapping.
This cannot fail, since the mapping starts out with
all free variables and the lambdas are added as they are encountered.

> getVar :: SId -> U SId
> getVar v = do
>     (_, m) <- get
>     return $ m M.! v
