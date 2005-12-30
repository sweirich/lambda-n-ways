The Simple module implements the Normal Form function by
using a naive version of substitution.

> module Simple(nf) where
> import Data.List(union, (\\))
> import Lambda
> import IdInt

> type SId = IdInt

The normal form is computed by repeatedly performing
substitution (beta reduction) on the leftmost redex.

> nf :: LC SId -> LC SId
> nf e@(Var _) = e
> nf (Lam x e) = Lam x (nf e)
> nf (App f a) =
>     case whnf f of
>         Lam x b -> nf (subst x a b)
>         f' -> App (nf f') (nf a)

Compute the head normal form.

> whnf :: LC SId -> LC SId
> whnf e@(Var _) = e
> whnf e@(Lam _ _) = e
> whnf (App f a) =
>     case whnf f of
>         Lam x b -> whnf (subst x a b)
>         f' -> App f' a

Substitution is done in the way it is often described.
When a name clash is detected we alpha convert the offending
lambda bound variable.  We find a new name by picking one that
is not in use locally.

> subst :: SId -> LC SId -> LC SId -> LC SId
> subst x s b = sub b
>  where sub e@(Var v) | v == x = s
>                      | otherwise = e
>        sub e@(Lam v e') | v == x = e
>                         | v `elem` fvs = Lam v' (sub e'')
>                         | otherwise = Lam v (sub e')
>                             where v' = newId vs
>                                   e'' = subst v (Var v') e'
>        sub (App f a) = App (sub f) (sub a)
>
>        fvs = freeVars s
>        vs = fvs `union` allVars b

Get a variable which is not in the given set.

> newId :: [SId] -> SId
> --newId vs = head ([ Id ("x" ++ show i) | i <- [0::Int .. ] ] \\ vs)
> newId vs = head ([ IdInt i | i <- [0::Int .. ] ] \\ vs)

Compute the free variables of an expression.

> freeVars :: LC SId -> [SId]
> freeVars (Var v) = [v]
> freeVars (Lam v e) = freeVars e \\ [v]
> freeVars (App f a) = freeVars f `union` freeVars a

Compute all variables in an expression.

> allVars :: LC SId -> [SId]
> allVars (Var v) = [v]
> allVars (Lam _ e) = allVars e
> allVars (App f a) = allVars f `union` allVars a

