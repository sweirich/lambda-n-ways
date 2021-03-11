-- | Generate a benchmark suite for normalization
--
-- Goal is to generate random sets of terms that
module QuickBench where

import Control.Monad
import qualified Data.List as List
import qualified DeBruijnPar.Scoped as Scoped
import Id
import IdInt
import Impl
import qualified Impl.Simple as Simple
import qualified Impl.Unique as Unique
import Lambda
import Misc
import Suite
import System.IO
import Test.QuickCheck

-- Stats for random.lam
-- sz: 100000
--   num substs: 26 26 26 26 28 28 29 29 29 29 30 32 32 33 33 34 35 36 38 39 40 43 44 59 177
--   bind depths: 23 27 29 30 32 32 33 33 33 34 34 34 36 37 37 40 40 40 40 44 44 46 46 46 57
--   depth:       36 42 44 45 45 47 48 48 49 49 50 50 51 52 53 53 56 56 56 60 60 60 61 62 73

-- Stats for random2.lam
-- sz: 100000
--   num substs: 26 26 26 26 27 27 27 27 28 28 29 29 29 29 29 30 30 31 32 32 32 33 34 36 36
--   bind depths: 13 15 22 27 27 29 29 31 31 33 33 34 35 36 36 38 39 39 40 41 41 41 43 44 46
--   depth:       23 23 37 40 41 44 44 45 46 47 47 49 50 51 52 53 53 53 54 55 55 56 58 60 60

{- stats about lennart.lam
   bind depth: 25
   depth:      53
   failed for:        1000
   failed for:        2000
   normalized steps:  4000
   num substs: 119697
-}

factStats :: IO ()
factStats = do
  contents <- readFile "timing.lam"
  let tm :: LC IdInt
      tm = toIdInt (read (stripComments contents) :: LC Id)
  putStrLn $ "   bind depth: " ++ show (maxBindingDepth tm)
  putStrLn $ "   depth:      " ++ show (depth tm)
  let loop n =
        case Simple.iNf n tm of
          Just (tm', ss) -> do
            putStrLn $ "   normalized steps:  " ++ show n
            putStrLn $ "   num substs: " ++ show (Simple.numSubsts ss)
          Nothing -> do
            putStrLn $ "   failed for:        " ++ show n
            loop (n * 2)
  loop 1000

-- | Use quickcheck to generate random lambda terms. Save the ones that actually do something
-- under normalization
data NfTerm = NfTerm
  { suite_before :: LC IdInt,
    suite_after :: LC IdInt,
    suite_numSubsts :: Int,
    suite_bindDepth :: Int,
    suite_depth :: Int
  }

mkNfTerm :: Int -> IO [NfTerm]
mkNfTerm sz = do
  let num = 100
  xs <- loop num []
  putStrLn $ "sz: " ++ show sz
  putStrLn $ "   num substs: " ++ unwords (map show (List.sort (map suite_numSubsts xs)))
  putStrLn $ "   bind depths: " ++ unwords (map show (List.sort (map suite_bindDepth xs)))
  putStrLn $ "   depth:       " ++ unwords (map show (List.sort (map suite_depth xs)))
  return xs
  where
    loop 0 tms = return tms
    loop n tms = do
      tm <- generate (resize sz (genScopedLam :: Gen (LC IdInt)))
      let stm = Scoped.toDB tm
      case Simple.iNf 2000 tm of
        Just (tm', ss) ->
          if not (tm `Lambda.aeq` tm') && Simple.numSubsts ss > 45
            then do
              putStrLn $ "Generation:" ++ show n
              let x =
                    NfTerm
                      { suite_before = tm,
                        suite_after = tm',
                        suite_numSubsts = Simple.numSubsts ss,
                        suite_bindDepth = maxBindingDepth tm,
                        suite_depth = depth tm
                      }
              loop (n -1) (x : tms)
            else loop n tms
        Nothing -> loop n tms

median :: (Ord a, Num a) => [a] -> a
median xs = List.sort xs !! (n `div` 2) where n = length xs

printNfTerm :: String -> [NfTerm] -> IO ()
printNfTerm fname xs = do
  f <- openFile ("lams/" ++ fname ++ ".lam") WriteMode
  fnf <- openFile ("lams/" ++ fname ++ ".nf.lam") WriteMode
  forM_ xs $ \x -> do
    hPutStrLn f ("-- numSubsts:  " ++ show (suite_numSubsts x))
    hPutStrLn f ("-- bind depth: " ++ show (suite_bindDepth x))
    hPutStrLn f ("-- depth:      " ++ show (suite_depth x))
    hPrint f (suite_before x)
  forM_ xs $ \x -> hPrint fnf (suite_after x)

{-
lams100.lam

sz: 10000
   num substs: 26 26 26 26 26 26 26 26 26 26 26 26 26 26 27 27 27 27 27 27 27 27 27 27 27 27 28 28 28 28 28 28 28 28 28 28 29 29 29 29 29 29 29 29 29 29 29 29 29 29 29 29 30 30 30 30 30 31 31 31 31 32 32 32 32 33 33 33 33 33 34 34 34 34 35 35 35 36 36 36 37 37 38 38 40 41 42 42 42 43 46 52 55 56 56 57 60 65 79 215
   bind depths: 16 18 19 19 19 21 22 24 24 24 24 24 25 25 25 25 26 26 26 26 26 26 27 27 27 27 27 27 28 28 28 28 28 28 28 29 29 29 29 29 29 30 30 30 30 31 31 31 31 31 31 31 31 31 31 31 31 32 32 32 32 32 32 32 33 33 33 33 33 33 33 34 34 34 34 34 34 35 35 36 36 36 37 37 37 37 38 39 40 40 40 40 41 42 42 43 45 47 47 51
   depth:       24 28 31 32 32 32 34 34 35 35 35 36 36 36 36 36 37 37 37 38 38 38 38 38 39 39 39 39 39 39 40 40 40 40 40 41 41 41 41 42 42 42 42 42 42 42 43 43 43 43 43 43 43 43 44 44 44 44 44 44 44 44 44 44 44 45 45 45 46 46 46 46 46 46 47 47 47 47 48 48 48 48 49 49 50 50 50 51 51 52 52 53 54 54 55 55 57 59 60 64

-}
