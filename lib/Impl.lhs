> {-# LANGUAGE TypeApplications #-}

> module Impl where

Every lambda calculus implementation must have a way to convert to and from
a "named" representation, a way to compute the normal form, and a way
to determine alpha-equivalence.  For uniformity, we package these components up
in a data structure. 

> import Imports 
> import Prelude hiding (abs)

> import Abstract.Simple as AS
> import Lambda
> import IdInt

> import qualified Abstract.Class as A

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

> unabs :: A.LC IdInt -> LC IdInt
> unabs (A.Var x)   = Var x
> unabs (A.Lam bnd) = let (x, a) = A.unbind' bnd in Lam x (unabs a)
> unabs (A.App a b) = App (unabs a) (unabs b)

> abs :: LC IdInt -> A.LC IdInt
> abs (Var x) = A.Var x
> abs (Lam x a) = A.lam' x (abs a)
> abs (App a b) = A.App (abs a)(abs b)

> fromBindingImpl :: forall v. A.BindingImpl v => Proxy v -> String -> LambdaImpl
> fromBindingImpl _ name = LambdaImpl {
>    impl_name = name , 
>    impl_fromLC = A.runBindM @v . A.fromLC . abs, 
>    impl_toLC = A.runBindM @v . fmap unabs . A.toLC, 
>    impl_nf = A.nf @v, 
>    impl_nfi = A.instrNormalize, 
>    impl_aeq = \x y -> A.runBindM @v (A.aeq x y)
>   }