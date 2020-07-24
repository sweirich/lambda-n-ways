{-# LANGUAGE RecordWildCards #-}
module Suite where

import qualified Misc
import Lambda
import IdInt
import Impl


import Impl.Simple
import Impl.SimpleB
import Impl.HOAS
import Impl.DeBruijn
import Impl.BoundDB
import Impl.Unbound
import Impl.UnboundGenerics
import Impl.Unique
--import Impl.NominalG

-- import DeBruijnC
import DeBruijnPar.P
import DeBruijnPar.F
import DeBruijnPar.B
import DeBruijnPar.FB
import DeBruijnPar.L
import DeBruijnPar.Scoped

import Core.Nf


import Test.QuickCheck

impls :: [LambdaImpl]
impls = [ 
          DeBruijnPar.F.impl
        , DeBruijnPar.FB.impl
        , DeBruijnPar.L.impl
        , DeBruijnPar.P.impl
        , DeBruijnPar.B.impl
        , DeBruijnPar.Scoped.impl
        , Impl.DeBruijn.impl
        , Impl.BoundDB.impl
        , Impl.HOAS.impl
        , Impl.SimpleB.impl
        , Impl.Simple.impl 
        , Impl.UnboundGenerics.impl 
        , Impl.Unbound.impl
        , Impl.Unique.impl
        , Core.Nf.impl  
        -- , Impl.NominalG.impl -- generally too slow (12s vs. <200 ms for everything else)
        ]

--------------------------------------------------------------
--------------------------------------------------------------

-- | Read a single term from a file
getTerm :: String -> IO (LC IdInt)
getTerm filename = do
   contents <- readFile filename
   let s = Misc.stripComments contents
   return $ toIdInt ((read :: String -> LC Id) s)

-- | Read a list of terms from a file
getTerms :: String -> IO [LC IdInt]
getTerms filename = do
   contents <- readFile filename
   let ss = lines (Misc.stripComments contents)
   return $ map (toIdInt . (read :: String -> LC Id)) ss


-- Convenience functions for creating test cases
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


{-
-- | Ok if either times out too early. But if they both finish, it should
-- be with the same answer
eqMaybe :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Property
eqMaybe f (Just x) (Just y) = classify True "aeq" (f x y)
eqMaybe _f _ _ = property True


prop_sameNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Int -> LC IdInt ->  Property
prop_sameNF f i x = eqMaybe Lambda.aeq (Simple.nfi i x) (f i x)


lc_nfi :: LambdaImpl -> Int -> LC IdInt -> Maybe (LC IdInt)
lc_nfi LambdaImpl{..} i x =
  impl_toLC <$>  impl_nfi i (impl_fromLC x)


-- NOTE: need "fueled" version of normalization 
-- NOTE: hard to shrink and stay well-closed
prop_closedNF :: LambdaImpl -> Property
prop_closedNF impl = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
      eqMaybe Unique.aeq (lc_nfi DeBruijn.impl 1000 x) (lc_nfi impl 1000 x)
-}
