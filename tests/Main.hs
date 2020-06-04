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

import Test.Tasty
import Test.Tasty.QuickCheck as QC 
import Test.Tasty.HUnit

-- reference version of LC IdInt alpha-equivalence
-- convert to DB indices and use (==)

ref_aeq :: LC IdInt -> LC IdInt -> Bool
ref_aeq x y = case DeBruijn.impl of
  LambdaImpl {..} -> impl_aeq (impl_fromLC x) (impl_fromLC y)
 
getTerm :: IO (LC Id)
getTerm = do
  contents <- readFile "timing.lam"
  return $ read (stripComments contents)
 

-- test the correctness by normalizing the benchmarking term
-- should produce result equal to false
main :: IO ()
main = do
   tm <- getTerm
   let tm1 = toIdInt tm
   let test_impl LambdaImpl{..} = do
         let result = (impl_toLC . impl_nf . impl_fromLC ) tm1 
         if Lambda.aeq lambda_false result then return ()
           else do
             putStrLn $ "FAILED: " ++ impl_name ++ " returned " ++ show result
             exitFailure
   forM_ impls test_impl



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
