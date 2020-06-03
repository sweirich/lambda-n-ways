> {-# LANGUAGE ExistentialQuantification #-}
> module Impl where

Every lambda calculus implementation must have a way to convert to and from
the "raw string" representation, a way to compute the normal form, and a way
to determine alpha-equivalence.  For uniformity, we package these components up
in a data structure. 

> import Control.DeepSeq

> import Lambda
> import IdInt

> data LambdaImpl =
>   forall a. NFData a =>
>       LambdaImpl
>          { impl_name   :: String ,
>            impl_fromLC :: LC IdInt -> a ,
>            impl_toLC   :: a -> LC IdInt,
>            impl_nf     :: a -> a,
>            impl_nfi    :: Int -> a -> Maybe a,
>            impl_aeq    :: a -> a -> Bool
> --           impl_fvs    :: a -> IdIntSet,
> --           impl_subst  :: a -> IdInt -> a -> a
>          }
