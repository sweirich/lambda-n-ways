The HOAS module implements the Normal Form function by
using Higher Order Abstract Syntax for the lambda expressions.
This makes it possible to use the native substitution of Haskell.

> module HOAS(nf) where
> import qualified Data.Map as M
> import Lambda
> import IdInt


> type SId = IdInt
>
> data HOAS = HVar SId | HLam (HOAS -> HOAS) | HApp HOAS HOAS

> nf :: LC SId -> LC SId
> nf = toLC . nfh . fromLC

> nfh :: HOAS -> HOAS
> nfh e@(HVar _) = e
> nfh (HLam b) = HLam (nfh . b)
> nfh (HApp f a) =
>     case whnf f of
>         HLam b -> nfh (b a)
>         f' -> HApp (nfh f') (nfh a)

Compute the head normal form.

> whnf :: HOAS -> HOAS
> whnf e@(HVar _) = e
> whnf e@(HLam _) = e
> whnf (HApp f a) =
>     case whnf f of
>         HLam b -> whnf (b a)
>         f' -> HApp f' a

Convert to higher order abstract syntax.  Do this by keeping
a mapping of the bound variables and translating them as they
are encountered.

> fromLC :: LC SId -> HOAS
> fromLC = from M.empty
>   where from m (Var v) = maybe (HVar v) id (M.lookup v m)
>         from m (Lam v e) = HLam $ \ x -> from (M.insert v x m) e
>         from m (App f a) = HApp (from m f) (from m a)

Convert back from higher order abstract syntax.  Do this by inventing
a new variable at each lambda.  For simplicity we just start the variable
numbering at 1000 rather than finding the free variables of the term.

> toLC :: HOAS -> LC SId
> toLC = to 1000
>   where to _ (HVar v) = Var v
>         to n (HLam b) = Lam i (to (n+1) (b (HVar i))) where i = IdInt n
>         to n (HApp f a) = App (to n f) (to n a)
