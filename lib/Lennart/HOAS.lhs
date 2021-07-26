The HOAS module implements the Normal Form function by
using Higher Order Abstract Syntax for the $\lambda$-expressions.
This makes it possible to use the native substitution of Haskell.

> module Lennart.HOAS(impl) where
> import qualified Data.Map as M
> import Util.Lambda hiding (aeq)
> import Util.IdInt
> import Control.DeepSeq
> import Data.Maybe(fromMaybe)


> import Util.Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>            impl_name   = "Lennart.HOAS"
>          , impl_fromLC = fromLC
>          , impl_toLC   = toLC
>          , impl_nf     = nf
>          , impl_nfi    = error "cannot implement nfi for HOAS"
>          , impl_aeq    = (==)
>       }


With higher order abstract syntax the abstraction in the implemented
language is represented by an abstraction in the implementation
language.
We still need to represent variables for free variables and also during
conversion.

> data HOAS = HVar IdInt | HLam (HOAS -> HOAS) | HApp HOAS HOAS
>
> instance NFData HOAS where
>   rnf (HVar i) = rnf i
>   rnf (HLam f) = rnf f
>   rnf (HApp a b) = rnf a `seq` rnf b

The substitution step for HOAS is simply a Haskell application since we
use a Haskell function to represent the abstraction.

> nf :: HOAS -> HOAS
> nf e@(HVar _) = e
> nf (HLam b) = HLam (nf . b)
> nf (HApp f a) =
>     case whnf f of
>         HLam b -> nf (b a)
>         f' -> HApp (nf f') (nf a)

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
>   where from m (Var v)  = fromMaybe (HVar v) (M.lookup v m)
>         from m (Lam v e) = HLam $ \ x -> from (M.insert v x m) e
>         from m (App f a) = HApp (from m f) (from m a)

Convert back from higher order abstract syntax.  Do this by inventing
a new variable at each $\lambda$.

> toLC :: HOAS -> LC IdInt
> toLC = to firstBoundId
>   where to _ (HVar v)   = Var v
>         to n (HLam b)   = Lam n (to (succ n) (b (HVar n)))
>         to n (HApp f a) = App (to n f) (to n a)

We can also use this idea when comparing for equality.

> maxVar :: HOAS -> IdInt
> maxVar (HVar x) = x
> maxVar (HLam b) = maxVar (b (HVar firstBoundId))
> maxVar (HApp a b) = max (maxVar a) (maxVar b)

> instance Eq HOAS where
>    (==) = aeq 

> aeq :: HOAS -> HOAS -> Bool
> aeq x y = aeqn m x y where
>   m = succ (max (maxVar x) (maxVar y))
>   aeqn _ (HVar v1) (HVar v2) = v1 == v2
>   aeqn n (HLam b1) (HLam b2) = aeqn (succ n) (b1 (HVar n)) (b2 (HVar n))
>   aeqn n (HApp a1 b1) (HApp a2 b2) = aeqn n a1 a2 && aeqn n b1 b2