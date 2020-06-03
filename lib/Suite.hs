{-# LANGUAGE RecordWildCards #-}
module Suite(impls) where

import Lambda
import IdInt
import Impl

import Simple
import SimpleB
import Unique
import HOAS
import DeBruijn
-- import DeBruijnC
import DeBruijnParF
import DeBruijnParB
import BoundDB
import Unbound
import UnboundGenerics
import DeBruijnScoped
import Core.Nf

import Test.QuickCheck

impls :: [LambdaImpl]
impls = [ DeBruijnParB.impl
        , DeBruijnScoped.impl
        , BoundDB.impl
        , HOAS.impl
        , SimpleB.impl
        , DeBruijnParF.impl
        , Simple.impl 
        , DeBruijn.impl
        , UnboundGenerics.impl 
        , Unbound.impl
        , Unique.impl
        , Core.Nf.impl
        ]

--------------------------------------------------------------
--------------------------------------------------------------



infixl 5 @@
(@@) :: LC IdInt -> LC IdInt -> LC IdInt
a @@ b  = App a b
lam :: Int -> LC IdInt -> LC IdInt
lam i b = Lam (IdInt i) b
var :: Int -> LC IdInt
var i   = Var (IdInt i)


lambda_true :: LC IdInt
lambda_true = lam 0 (lam 1 (var 0))

lambda_false :: LC IdInt
lambda_false = lam 0 (lam 1 (var 1))

prop_rt :: LambdaImpl -> LC IdInt -> Bool
prop_rt LambdaImpl{..} x = impl_toLC (impl_fromLC x) `Lambda.aeq` x

prop_aeq :: Property
prop_aeq = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
   forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \y ->
       let eq = Lambda.aeq x y in
       classify eq "aeq" $ eq == (DeBruijn.toDB x == DeBruijn.toDB y)


eqMaybe :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Property
eqMaybe f (Just x) (Just y) = classify True "aeq" (f x y)
eqMaybe _f _ _ = property True


prop_sameNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Int -> LC IdInt ->  Property
prop_sameNF f i x = eqMaybe Lambda.aeq (Simple.nfi i x) (f i x)

-- NOTE: need "fueled" version of normalization 
-- NOTE: hard to shrink and stay well-closed
prop_closedNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Property
prop_closedNF f = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
      eqMaybe Unique.aeq (DeBruijn.fromDB <$> DeBruijn.nfi 1000 (DeBruijn.toDB x)) (f 1000 x)
