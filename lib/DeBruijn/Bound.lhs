The DeBruijn module implements the Normal Form function by
using de Bruijn indicies.

> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE StandaloneDeriving #-}
> module DeBruijn.Bound(nf,DeBruijn.Bound.aeq,toDB,fromDB,nfd, impl) where
> import Lambda
> import IdInt
> import Data.Functor.Classes (Eq1(..))

> import Control.Monad
> import GHC.Generics hiding (to,from)
> import Control.DeepSeq
> 
> import Bound

> import Impl
> impl :: LambdaImpl
> impl = LambdaImpl {
>            impl_name   = "Bound"
>          , impl_fromLC = toDB
>          , impl_toLC   = fromDB
>          , impl_nf     = nfd
>          , impl_nfi    = error "nfi unimplemented for BoundDB"
>          , impl_aeq    = (==)
>       }


Variables are represented by their binding depth, i.e., how many
$\lambda$s out the binding $\lambda$ is.  Free variables are represented
by negative numbers.

> data DB a = DVar a | DLam (Scope () DB a) | DApp (DB a) (DB a)
>   deriving (Functor, Foldable, Traversable, Generic)

> instance NFData a => NFData (DB a)
> deriving instance Eq a => (Eq (DB a))
>
> instance Eq1 DB where
>   liftEq f (DVar x) (DVar y) = f x y
>   liftEq f (DLam s1) (DLam s2) = liftEq f s1 s2
>   liftEq f (DApp a1 b1) (DApp a2 b2) = liftEq f a1 a2 && liftEq f b1 b2
>   liftEq _ _ _ = False

> instance Applicative DB where
>   pure = DVar
>   (<*>) = ap

> instance Monad DB where
>   return = DVar
>   DVar a   >>= f = f a
>   DApp x y >>= f = DApp (x >>= f) (y >>= f)
>   DLam x   >>= f = DLam (x >>>= f)

> aeq :: LC IdInt -> LC IdInt -> Bool
> aeq x y = toDB x == toDB y
>

> nf :: LC IdInt -> LC IdInt
> nf = fromDB . nfd . toDB

Computing the normal form proceeds as usual.

> nfd :: DB a -> DB a
> nfd e@(DVar _) = e
> nfd (DLam e) = DLam $ toScope $ nfd $ fromScope e
> nfd (DApp f a) =
>     case whnf f of
>         DLam b -> nfd (instantiate1 a b)
>         f' -> DApp (nfd f') (nfd a)

Compute the weak head normal form.

> whnf :: DB a -> DB a
> whnf e@(DVar _) = e
> whnf e@(DLam _) = e
> whnf (DApp f a) =
>     case whnf f of
>         DLam b -> whnf (instantiate1 a b)
>         f' -> DApp f' a


Convert from LC type to DB type

> toDB :: LC IdInt -> DB IdInt
> toDB = to 
>   where to :: LC IdInt -> DB IdInt
>         to (Var v)   = DVar v
>         to (Lam v b) = DLam (abstract1 v (to b))
>         to (App f a) = DApp (to  f) (to a)

Convert back from deBruijn to the LC type.

> fromDB :: DB IdInt -> LC IdInt
> fromDB = from firstBoundId
>   where from :: IdInt -> DB IdInt -> LC IdInt
>         from   _ (DVar v) = Var v
>         from n (DLam b)   = Lam n (from (succ n) (instantiate1 (DVar n) b))
>         from n (DApp f a) = App (from n f) (from n a) 


