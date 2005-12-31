The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

> module DeBruijn(nf) where
> import List(elemIndex)
> import Lambda
> import IdInt

> type SId = IdInt

Variables are represented by their binding depth, i.e., how many
lambdas out the binding lambda is.  Free variables are represented
by negative numbers.

> data DB = DVar Int | DLam DB | DApp DB DB

> nf :: LC SId -> LC SId
> nf = fromDB . nfd . toDB

> nfd :: DB -> DB
> nfd e@(DVar _) = e
> nfd (DLam e) = DLam (nfd e)
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> nfd (subst 0 a b)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form.

> whnf :: DB -> DB
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (subst 0 a b)
>         f' -> DApp f' a

> fromDB :: DB -> LC SId
> fromDB e = from 2000 e
>   where from n (DVar i) | i < 0 = Var (IdInt (-i))
>                         | otherwise = Var (IdInt (n-i-1))
>         from n (DLam b) = Lam (IdInt n) (from (n+1) b)
>         from n (DApp f a) = App (from n f) (from n a)

> toDB :: LC SId -> DB
> toDB e = to [] e
>   where to vs (Var v@(IdInt i)) = maybe (DVar (-i)) DVar (elemIndex v vs)
>         to vs (Lam x b) = DLam (to (x:vs) b)
>         to vs (App f a) = DApp (to vs f) (to vs a)

> subst :: Int -> DB -> DB -> DB
> subst o s v@(DVar i) | i == o = adjust 0 s
>                      | otherwise = v
>   where adjust n e@(DVar j) | j >= n = DVar (i+o)
>                             | otherwise = e
>         adjust n (DLam e) = DLam (adjust (n+1) e)
>         adjust n (DApp f a) = DApp (adjust n f) (adjust n a)
> subst o s (DLam e) = DLam (subst (o+1) s e)
> subst o s (DApp f a) = DApp (subst o s f) (subst o s a)
