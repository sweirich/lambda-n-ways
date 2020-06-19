{-# LANGUAGE RecordWildCards #-}
module Main where

import Misc
import Lambda as Lambda
import IdInt
import Impl
import Suite
import System.Exit (exitFailure)
import Control.Monad
import Test.QuickCheck

import qualified DeBruijn
import qualified Unique

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck as QC 
import Test.Tasty.HUnit


-- | Reference version of aeq
-- convert to DB indices and use (==)
db_aeq :: LC IdInt -> LC IdInt -> Bool
db_aeq t1 t2 = DeBruijn.toDB t1 == DeBruijn.toDB t2

-- | Reference version of nf
-- convert to DB indices first
db_nf :: LC IdInt -> LC IdInt
db_nf tm = DeBruijn.fromDB (DeBruijn.nfd (DeBruijn.toDB tm))

-------------------------------------------------------------------
-- Conversion to/from LC tests
-- make sure round-trip is identity

prop_rt :: LambdaImpl -> Property
prop_rt LambdaImpl{..} = withMaxSuccess 1000 $ forAllShrink IdInt.genScoped IdInt.shrinkScoped  $ \x ->
  impl_toLC (impl_fromLC x) `db_aeq` x

rtQCs :: TestTree
rtQCs = testGroup "Conv QC tests" (map f impls) where
  f i = testProperty (impl_name i) (prop_rt i)

-------------------------------------------------------------------
-- Alpha-equivalence tests

-- | Make sure that a "freshened" version of a term is alpha-equivalent to itself
prop_aeq :: LambdaImpl -> Property
prop_aeq LambdaImpl{..} = withMaxSuccess 1000 $ forAllShrink IdInt.genScoped IdInt.shrinkScoped  $ \x -> 
  let x' = impl_fromLC x
      y' = impl_fromLC y
      y  = Unique.fromUnique (Unique.toUnique x)
  in property (x' `impl_aeq` y') 

-- | Convert prop above into Tasty test
aeqQCs :: TestTree
aeqQCs = testGroup "AEQ QC tests" (map f impls) where
  f i = testProperty (impl_name i) (Main.prop_aeq i) 


-------------------------------------------------------------------
-- Fueled Normalization matches original

-- | Quick-check based tests for normalization, compare with reference version
-- Note: must use fueled version becase random terms may not terminate
prop_fueled_nf :: LambdaImpl -> Property
prop_fueled_nf LambdaImpl{..} = withMaxSuccess 1000 $ forAllShrink genScopedLam shrinkScoped $ \tm1 -> do
   case (impl_nfi 1000 (impl_fromLC tm1)) of
     Just result -> property (impl_aeq (impl_nf (impl_fromLC tm1)) result)
     Nothing -> classify True "nonterminating" $ property True                       

nfFueledQCs :: TestTree
nfFueledQCs = testGroup "NF fueled quick checks" (map f impls) where
  f i = testProperty (impl_name i) (prop_fueled_nf i)


-------------------------------------------------------------------
-- Normalization tests



-- | Pre-set random tests for normalization
nfRandomTests :: IO TestTree
nfRandomTests = do
  inputs <- getTerms "lams/random.lam"
  outputs <- getTerms "lams/random.nf2.lam"
  let test_impl :: LambdaImpl -> LC IdInt -> LC IdInt -> TestTree
      test_impl LambdaImpl{..} tm1 tm2 = do
         let result = (impl_toLC . impl_nf . impl_fromLC ) tm1 
         testCase "" (assertBool ("orig tm:     " ++ show tm1
                                  ++ "\nnf produced: " ++ show result
                                  ++ "\nshould be:   " ++ show tm2) (db_aeq tm2 result))
  return $ testGroup "NF Unit Tests" $
    map (\i -> testGroup (impl_name i) $ zipWith (test_impl i) inputs outputs) impls 

-- | Quick-check based tests for normalization, compare with reference version
-- Note: must use fueled version becase random terms may not terminate
prop_nf :: LambdaImpl -> Property
prop_nf LambdaImpl{..} = withMaxSuccess 1000 $ forAllShrink genScopedLam shrinkScoped $ \tm1 -> do
   case (impl_toLC <$> (impl_nfi 1000 (impl_fromLC tm1))) of
     Just result -> do let tm2    = db_nf tm1
                       property (db_aeq tm2 result)
     Nothing -> classify True "nonterminating" $ property True                       

nfQCs :: TestTree
nfQCs = testGroup "NF quick checks" (map f impls) where
  f i = testProperty (impl_name i) (prop_nf i)

-- | Unit test based on normalizing large lambda term
nfUnitTests :: IO TestTree
nfUnitTests = do
  tm <- getTerm "lams/lennart.lam"
  let tm1 = toIdInt tm
  let test_impl LambdaImpl{..} = do
         let result = (impl_toLC . impl_nf . impl_fromLC ) tm1 
         assertBool ("nf produced: " ++ show result) (db_aeq lambda_false result)
  return $ testGroup "NF Unit Tests" $
    map (\i -> testCase (impl_name i) $ test_impl i) impls 

-- test the correctness by normalizing the benchmarking term
-- should produce result equal to false
main :: IO ()
main = do
  nfTests <- nfUnitTests
  nfRandomTests <- nfRandomTests
  defaultMain $ testGroup "tests" [rtQCs, aeqQCs, nfQCs, nfFueledQCs, nfRandomTests, nfTests]


