The HOAS module implements the Normal Form function by
using Higher Order Abstract Syntax for the $\lambda$-expressions.
This makes it possible to use the native substitution of Haskell.

> module HOAS(nf) where
> import qualified Data.Map as M
> import Lambda
> import IdInt

With higher order abstract syntax the abstraction in the implemented
language is represented by an abstraction in the implementation
language.
We still need to represent variables for free variables and also during
conversion.

> data HOAS = HVar IdInt | HLam (HOAS -> HOAS) | HApp HOAS HOAS

To compute the normal form, first convert to HOAS, compute, and
convert back.

> nf :: LC IdInt -> LC IdInt
> nf = toLC . nfh . fromLC

The substitution step for HOAS is simply a Haskell application since we
use a Haskell function to represent the abstraction.

> nfh :: HOAS -> HOAS
> nfh e@(HVar _) = e
> nfh (HLam b) = HLam (nfh . b)
> nfh (HApp f a) =
>     case whnf f of
>         HLam b -> nfh (b a)
>         f' -> HApp (nfh f') (nfh a)

Compute the weak head normal form.

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

> fromLC :: LC IdInt -> HOAS
> fromLC = from M.empty
>   where from m (Var v) = maybe (HVar v) id (M.lookup v m)
>         from m (Lam v e) = HLam $ \ x -> from (M.insert v x m) e
>         from m (App f a) = HApp (from m f) (from m a)

Convert back from higher order abstract syntax.  Do this by inventing
a new variable at each $\lambda$.

> toLC :: HOAS -> LC IdInt
> toLC = to firstBoundId
>   where to _ (HVar v) = Var v
>         to n (HLam b) = Lam n (to (succ n) (b (HVar n)))
>         to n (HApp f a) = App (to n f) (to n a)
