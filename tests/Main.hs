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

-- | reference version of LC IdInt alpha-equivalence
-- convert to DB indices and use (==)
ref_aeq :: LC IdInt -> LC IdInt -> Bool
ref_aeq x y = case DeBruijn.impl of
  LambdaImpl {..} -> impl_aeq (impl_fromLC x) (impl_fromLC y)

aeq :: LambdaImpl -> LC IdInt -> LC IdInt -> Bool
aeq LambdaImpl{..} x y = x' `impl_aeq` y' where
    x' = impl_fromLC x
    y' = impl_fromLC y



prop_aeqScoped :: LambdaImpl -> Property
prop_aeqScoped LambdaImpl{..} = withMaxSuccess 1000 $ forAllShrink IdInt.genScoped IdInt.shrinkScoped  $ \x -> 
  let x' = impl_fromLC x
      y' = impl_fromLC y
      y  = Unique.fromUnique (Unique.toUnique x)
  in property (x' `impl_aeq` y') 


prop_aeq :: LambdaImpl -> Property
prop_aeq LambdaImpl{..} = withMaxSuccess 1000 $ forAll arbitrary  $ \x -> 
  let x' = impl_fromLC x
      y' = impl_fromLC y
      y  = Unique.fromUnique (Unique.toUnique x)
  in property (x' `impl_aeq` y') 
  

aeqQCs :: TestTree
aeqQCs = testGroup "AEQ unit tests" (map f impls) where
  f i = testProperty (impl_name i) (Main.prop_aeqScoped i) 

-- Unit tests from the benchmark (normalizing the giant lambda term)  
getTerm :: IO (LC Id)
getTerm = do
  contents <- readFile "timing.lam"
  return $ read (stripComments contents)

-- Random tests 
getRandomTerms :: IO ([LC IdInt], [LC IdInt])
getRandomTerms = do
   contents <- readFile "random.lam"
   let ss = lines (stripComments contents)
   let inputs = map (toIdInt . (read :: String -> LC Id)) ss
   contents <- readFile "random.nf2.lam"
   let ss = lines (stripComments contents)
   let outputs = map (toIdInt . (read :: String -> LC Id)) ss
   return (inputs, outputs)

nfRandomTests :: IO TestTree
nfRandomTests = do
  (inputs, outputs) <- getRandomTerms
  let test_impl :: LambdaImpl -> LC IdInt -> LC IdInt -> TestTree
      test_impl LambdaImpl{..} tm1 tm2 = do
         let result = (impl_toLC . impl_nf . impl_fromLC ) tm1 
         testCase "" (assertBool ("nf produced: " ++ show result ++ "\nshould be:   " ++ show tm2) (db_aeq tm2 result))
  return $ testGroup "NF Unit Tests" $
    map (\i -> testGroup (impl_name i) $ zipWith (test_impl i) inputs outputs) impls 

db_aeq :: LC IdInt -> LC IdInt -> Bool
db_aeq t1 t2 = DeBruijn.toDB t1 == DeBruijn.toDB t2


nfUnitTests :: IO TestTree
nfUnitTests = do
  tm <- getTerm
  let tm1 = toIdInt tm
  let test_impl LambdaImpl{..} = do
         let result = (impl_toLC . impl_nf . impl_fromLC ) tm1 
         assertBool ("nf produced: " ++ show result) (Lambda.aeq lambda_false result)
  return $ testGroup "NF Unit Tests" $
    map (\i -> testCase (impl_name i) $ test_impl i) impls 

-- test the correctness by normalizing the benchmarking term
-- should produce result equal to false
main :: IO ()
main = do
  nfTests <- nfUnitTests
  nfRandomTests <- nfRandomTests
  defaultMain $ testGroup "tests" [nfRandomTests] -- aeqQCs, nfTests


{-

-- test case that demonstrates the issue with renaming with a bound variable
-- the simplifications to t2 and t3 below do not demonstrate the bug, only t1
-- note how x3 is already in scope, 

> t1 :: LC IdInt
> t1 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>         (  (lam 1 (lam 2 (lam 3 ( var 1 @@ (lam 4 (var 4)))))) @@
>            (  (lam 1 (lam 2 ((lam 3 (var 2)) @@ (var 1 @@ var 3)))) @@
>               (lam 1 (lam 2 (var 3)))))))))


\x0.\x1.\x2.\x3.\x4.(\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.(\x3.x2) (x1 x3)) (\x1.\x2.x3))

\x0.\x1.\x2.\x3.\x4.
    (\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.(\x3.x2) (x1 x3)) (\x1.\x2.x3))
-->
    (\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.x2) (\x1.\x2.x3))

> t2 :: LC IdInt
> t2 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>         (  (lam 1 (lam 2 (lam 3 ( var 1 @@ (lam 4 (var 4)))))) @@
>            (  (lam 1 (lam 2 (var 2))) @@
>               (lam 1 (lam 2 (var 3)))))))))


\x0.\x1.\x2.\x3.\x4.\x1.\x2.(\x3.x2) (x1 x3)




> t3 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>          (lam 1 (lam 2 ((lam 3 (var 2)) @@ (var 1 @@ var 3))))))))

\x0.\x1.\x2.\x3.\x4.
   (\x1.x1 ((\x2.x1) (\x2.x2) (\x2.x2 x1))) (\x1.\x2.(\x3.\x4.x1) (\x3.x3 x2))

> t4 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>        ((lam 1 (var 1 @@ ((lam 2 (var 1)) @@ (lam 2 (var 2)) @@ (lam 2 (var 2 @@ var 1)))))
>        @@
>        (lam 1 (lam 2 ( (lam 3 (lam 4 (var 1))) @@ (lam 3 (var 3 @@ var 2))))))))))

-- Counterexample for Core

> t5 :: LC IdInt
> t5 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4 (lam 1 (lam 2 (lam 3 (lam 4 (lam 5 (var 1 @@ var 3))))))))))

-}
