The Simple module implements the Normal Form function by
using a na\"{i}ve version of substitution.

> module Simple(nf,nfi) where
> import Data.List(union, (\\))
> import Lambda
> import IdInt


The normal form is computed by repeatedly performing
substitution ($\beta$-reduction) on the leftmost redex.
Variables and abstractions are easy, but in the case of
an application we must compute the function to see if
it is an abstraction.  The function cannot be computed
with the {\tt nf} function since it could perform
non-leftmost reductions.  Instead we use the {\tt whnf}
function.

> nf :: LC IdInt -> LC IdInt
> nf e@(Var _) = e
> nf (Lam x e) = Lam x (nf e)
> nf (App f a) =
>     case whnf f of
>         Lam x b -> nf (subst x a b)
>         f' -> App (nf f') (nf a)

> nfi :: Int -> LC IdInt -> Maybe (LC IdInt)
> nfi 0 _e = Nothing
> nfi _n e@(Var _) = return  e
> nfi n (Lam x e) = Lam x <$> nfi (n-1) e
> nfi n (App f a) = do
>     f' <- whnfi (n - 1) f 
>     case f' of
>         Lam x b -> nfi (n-1) (subst x a b)
>         _ -> App <$> nfi (n-1) f' <*> nfi (n-1) a



Compute the weak head normal form.  It is similar to computing the normal form,
but it does not reduce under $\lambda$, nor does it touch an application
that is not a $\beta$-redex.

> whnf :: LC IdInt -> LC IdInt
> whnf e@(Var _) = e
> whnf e@(Lam _ _) = e
> whnf (App f a) =
>     case whnf f of
>         Lam x b -> whnf (subst x a b)
>         f' -> App f' a


> whnfi :: Int -> LC IdInt -> Maybe (LC IdInt)
> whnfi 0 _e = Nothing 
> whnfi _n e@(Var _) = return e
> whnfi _n e@(Lam _ _) = return e
> whnfi n (App f a) = do
>     f' <- whnfi (n - 1) f 
>     case f' of
>         Lam x b -> whnfi (n - 1) (subst x a b)
>         _ -> return $ App f' a


Substitution has only one interesting case, the abstraction.
For abstraction there are three cases:
if the bound variable, {\tt v}, is equal to the variable we
are replacing, {\tt x}, then we are done,
if the bound variable is in set set of free variables
of the substituted expression then there would be
an accidental capture and we rename it,
otherwise the substitution just continues.

How should the new variable be picked when doing the
renaming?  The new variable must not be in the set of
free variables of {\tt s} since this would case another
accidental capture, nor must it be among the free variables
of {\tt e'} since this could cause another accidental
capture.  Conservatively, we avoid all variables occuring
in the original {\tt b} to fulfill the second requirement.

> subst :: IdInt -> LC IdInt -> LC IdInt -> LC IdInt
> subst x s b = sub vs0 b
>  where sub _ e@(Var v) | v == x = s
>                        | otherwise = e
>        sub vs e@(Lam v e') | v == x = e
>                            | v `elem` fvs = Lam v' (sub (v':vs) e'')
>                            | otherwise = Lam v (sub (v:vs) e')
>                             where v' = newId vs
>                                   e'' = subst v (Var v') e'
>        sub vs (App f a) = App (sub vs f) (sub vs a)
>
>        fvs = freeVars s
>        vs0 = fvs `union` allVars b

(Note: updated according to Kmett's blog post
 https://www.schoolofhaskell.com/user/edwardk/bound.)

Get a variable which is not in the given set.
Do this simply by generating all variables and picking the
first not in the given set.

> newId :: [IdInt] -> IdInt
> newId vs = head ([firstBoundId .. ] \\ vs)

