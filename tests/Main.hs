{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Monad
import qualified DeBruijn.Lennart as DeBruijn
import qualified Named.Unique as Unique
import Suite
import System.Exit (exitFailure)
import Test.QuickCheck
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Util.IdInt
import Util.Impl
import Util.Misc
import qualified Util.Stats as Stats
import Util.Syntax.Lambda

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
prop_rt LambdaImpl {..} = withMaxSuccess 1000 $
  forAllShrink genScoped shrinkScoped $ \x ->
    impl_toLC (impl_fromLC x) `db_aeq` x

rtQCs :: TestTree
rtQCs = testGroup "Conv QC tests" (map f impls)
  where
    f i = testProperty (impl_name i) (prop_rt i)

-------------------------------------------------------------------
-- Alpha-equivalence tests

-- | Make sure that a "freshened" version of a term is alpha-equivalent to itself
prop_aeq :: LambdaImpl -> Property
prop_aeq LambdaImpl {..} = withMaxSuccess 1000 $
  forAllShrink genScoped shrinkScoped $ \x ->
    let x' = impl_fromLC x
        y' = impl_fromLC y
        y = Unique.fromUnique (Unique.toUnique x)
     in property (x' `impl_aeq` y')

-- | Convert prop above into Tasty test
aeqQCs :: TestTree
aeqQCs = testGroup "AEQ QC tests" (map f impls)
  where
    f i = testProperty (impl_name i) (Main.prop_aeq i)

-------------------------------------------------------------------
-- Normalization tests

-- | Pre-set random tests for normalization
nfRandomTests :: String -> IO TestTree
nfRandomTests str = do
  inputs <- getTerms $ "lams/" ++ str ++ ".lam"
  outputs <- getTerms $ "lams/" ++ str ++ ".nf.lam"
  let test_impl :: LambdaImpl -> LC IdInt -> LC IdInt -> TestTree
      test_impl LambdaImpl {..} tm1 tm2 = do
        let result = (impl_toLC . impl_nf . impl_fromLC) tm1
        testCase
          ""
          ( assertBool
              ( "orig tm:     " ++ show tm1
                  ++ "\nnf produced: "
                  ++ show result
                  ++ "\nshould be:   "
                  ++ show tm2
              )
              (db_aeq tm2 result)
          )
  return $
    testGroup ("NF random tests: " ++ str) $
      map (\i -> testGroup (impl_name i) $ zipWith (test_impl i) inputs outputs) impls

------------------------------------------------------------------------------

compareNf :: LC IdInt -> LambdaImpl -> Assertion
compareNf tm1 =
  let iters = 5000
   in case Stats.runM (DeBruijn.nfi iters (DeBruijn.toDB tm1)) of
        Just (db_ct, result) ->
          let db_tm = DeBruijn.fromDB result
           in \LambdaImpl {..} ->
                case Stats.runM (impl_nfi iters (impl_fromLC tm1)) of
                  Just (impl_ct, impl_tm) -> do
                    let impl_res = (impl_toLC impl_tm)
                    assertBool
                      ("nf produced: " ++ show impl_res)
                      (db_aeq db_tm impl_res)
                    assertBool ("step mismatch: " ++ show impl_ct ++ " vs. " ++ show db_ct) (impl_ct == db_ct)
                  Nothing -> assertBool "no result produced" False
        Nothing -> error $ "no nf after" ++ show iters

-- | Quick-check based tests for normalization, compare with reference version
-- Note: must use fueled version of DB normalization becase random terms may not terminate
-- Uses DB version of aeq to compare results
prop_nf :: LambdaImpl -> Property
prop_nf LambdaImpl {..} = withMaxSuccess 5000 $
  forAllShrink genScopedLam shrinkScoped $ \tm1 -> do
    case Stats.runM (DeBruijn.nfi 2000 (DeBruijn.toDB tm1)) of
      Just (db_ct, result) ->
        let db_tm = DeBruijn.fromDB result
         in if db_aeq tm1 db_tm
              then discard
              else
                classify (db_ct == Stats.Stats 1) "stats == 1" $
                  classify (db_ct == Stats.Stats 2) "stats == 2" $
                    classify (db_ct == Stats.Stats 3) "stats == 3" $
                      classify (db_ct == Stats.Stats 4) "stats == 4" $
                        classify (db_ct >= Stats.Stats 5) "stats >= 5" $
                          ( case Stats.runM (impl_nfi 2000 (impl_fromLC tm1)) of
                              Just (impl_ct, impl_tm) ->
                                property (db_aeq (impl_toLC impl_tm) db_tm) .&&. impl_ct == db_ct
                              Nothing -> property False
                          )
      Nothing -> classify True "nonterminating" $ property True

nfQCs :: TestTree
nfQCs = testGroup "nfi vs. deBruijn" (map f impls)
  where
    f i = testProperty (impl_name i) (prop_nf i)

-- | Quick-check based tests for normalization, compare with fueled version
-- Make sure that the fueled normalization matches full normalization
-- Uses impl version of aeq to compare results
prop_fueled_nf :: LambdaImpl -> Property
prop_fueled_nf LambdaImpl {..} = withMaxSuccess 1000 $
  forAllShrink genScopedLam shrinkScoped $ \tm1 -> do
    case Stats.runM (impl_nfi 1000 (impl_fromLC tm1)) of
      Just (_, result) -> property (impl_aeq (impl_nf (impl_fromLC tm1)) result)
      Nothing -> classify True "nonterminating" $ property True

nfFueledQCs :: TestTree
nfFueledQCs = testGroup "nfi vs nf" (map f impls)
  where
    f i = testProperty (impl_name i) (prop_fueled_nf i)

--------------------------------------------------------

-- | Unit test based on normalizing large lambda term
nfLennartUnitTests :: IO TestTree
nfLennartUnitTests = do
  tm <- getTerm "lams/lennart.lam"
  let tm1 = toIdInt tm
  let test_impl LambdaImpl {..} = do
        let result = (impl_toLC . impl_nf . impl_fromLC) tm1
        assertBool ("nf produced: " ++ show result) (db_aeq lambdaFalse result)
  -- let test_impl li = (compareNf tm1 li)
  return $
    testGroup "NF Unit Test (Lennart) " $
      map (\i -> testCase (impl_name i) $ test_impl i) impls

main :: IO ()
main = do
  strictness <- mapM nfRandomTests ["full", "full-2"] -- "random25-20"]
  nfRandoms <- mapM nfRandomTests ["random", "random2", 
                 "random15", "random20", "random25", "random35", "lams100"] -- random25
  nfLamTests <- mapM nfRandomTests ["t1", "t2", "t3", "t4", "t5", "t6", "t7"]
  nfFull <- mapM nfRandomTests ["full"]
  nfSimple <- mapM nfRandomTests ["capture10", "constructed10"]
  nfMoreTests <- mapM nfRandomTests ["tests", "onesubst", "twosubst", "threesubst", "foursubst"]
  lt <- nfLennartUnitTests

  defaultMain $ testGroup "tests" $ 
      strictness ++ nfLamTests ++ nfSimple ++ nfMoreTests ++ nfRandoms ++ [lt]
                 ++ nfFull

-- defaultMain $ testGroup "tests" ([rtQCs, aeqQCs, nfQCs] ++ nfRandoms ++ nfLamTests ++ nfSimple ++ nfMoreTests ++ [lt])
