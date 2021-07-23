-- | Generate a benchmark suite for normalization
--
-- Goal is to generate random sets of terms that have certain properties
-- (i.e. number of substitutions during normalization, a large number of nested binders,
-- deep overall.)
-- This file is not run during benchmarking, but was used (via ghci) to generate the random
-- sets of lambda terms in the "lams" subdirectory.
module QuickBench where

import Control.Monad
import qualified Data.List as List
import qualified DeBruijn.Par.Scoped as Scoped
import qualified Lennart.Simple as Simple
import qualified Lennart.Unique as Unique
import Suite
import System.IO
import Test.QuickCheck
import Util.Id
import Util.IdInt
import Util.Impl
import Util.Lambda
import Util.Misc

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

-- stats for lams100.lam
-- sz: 10000
--   num substs: 26 26 26 26 26 26 26 26 26 26 26 26 26 26 27 27 27 27 27 27 27 27 27 27 27 27 28 28 28 28 28 28 28 28 28 28 29 29 29 29 29 29 29 29 29 29 29 29 29 29 29 29 30 30 30 30 30 31 31 31 31 32 32 32 32 33 33 33 33 33 34 34 34 34 35 35 35 36 36 36 37 37 38 38 40 41 42 42 42 43 46 52 55 56 56 57 60 65 79 215
--   bind depths: 16 18 19 19 19 21 22 24 24 24 24 24 25 25 25 25 26 26 26 26 26 26 27 27 27 27 27 27 28 28 28 28 28 28 28 29 29 29 29 29 29 30 30 30 30 31 31 31 31 31 31 31 31 31 31 31 31 32 32 32 32 32 32 32 33 33 33 33 33 33 33 34 34 34 34 34 34 35 35 36 36 36 37 37 37 37 38 39 40 40 40 40 41 42 42 43 45 47 47 51
--   depth:       24 28 31 32 32 32 34 34 35 35 35 36 36 36 36 36 37 37 37 38 38 38 38 38 39 39 39 39 39 39 40 40 40 40 40 41 41 41 41 42 42 42 42 42 42 42 43 43 43 43 43 43 43 43 44 44 44 44 44 44 44 44 44 44 44 45 45 45 46 46 46 46 46 46 47 47 47 47 48 48 48 48 49 49 50 50 50 51 51 52 52 53 54 54 55 55 57 59 60 64

{- stats for lennart.lam
   bind depth: 25
   depth:      53
   normalized steps:  2000 - 4000
   num substs: 119697
-}
-- Calculate stats for a single term
factStats :: String -> IO ()
factStats fname = do
  contents <- readFile $ "lams/" ++ fname
  let tm :: LC IdInt
      tm = toIdInt (read (stripComments contents) :: LC Id)
  putStrLn $ "   bind depth: " ++ show (maxBindingDepth tm)
  putStrLn $ "   depth:      " ++ show (depth tm)
  let loop n =
        case Simple.iNf n tm of
          Just (_, ss) -> do
            putStrLn $ "   normalized steps:  " ++ show n
            putStrLn $ "   num substs: " ++ show (Simple.numSubsts ss)
          Nothing -> do
            putStrLn $ "   failed for:        " ++ show n
            loop (n * 2)
  loop 1000

-- calculate stats for a file of terms

-- | Use quickcheck to generate random lambda terms. Save the ones that actually do something
-- under normalization
data NfTerm = NfTerm
  { suite_before :: LC IdInt,
    suite_after :: LC IdInt,
    suite_numSubsts :: Int,
    suite_bindDepth :: Int,
    suite_depth :: Int
  }

readLams :: String -> IO [LC IdInt]
readLams fname = do
  contents <- readFile $ "lams/" ++ fname ++ ".lam"
  return $ map parse (nonblankLines (stripComments contents))
  where
    parse :: String -> LC IdInt
    parse s = toIdInt (read s :: LC Id)

nfTerms :: [LC IdInt] -> IO [NfTerm]
nfTerms tms = do
  forM tms $ \tm -> do
    let stm = Scoped.toDB tm
    case Simple.iNf 2000 tm of
      Just (tm', ss) ->
        if not (tm `Util.Lambda.aeq` tm')
          then do
            return $
              NfTerm
                { suite_before = tm,
                  suite_after = tm',
                  suite_numSubsts = Simple.numSubsts ss,
                  suite_bindDepth = maxBindingDepth tm,
                  suite_depth = depth tm
                }
          else do
            putStrLn "Term did not change"
            error "Cannot normalize this set"
      Nothing -> do
        putStrLn $ "Failed to normalize"
        putStrLn $ show tm
        error "Cannot normalize this set"

arbitraryNfTerms :: Int -> IO [NfTerm]
arbitraryNfTerms sz = do
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
      case Simple.iNf 2000 tm of
        Just (tm', ss) ->
          if not (tm `Util.Lambda.aeq` tm') && Simple.numSubsts ss == 4
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

printNfTerms :: String -> [NfTerm] -> IO ()
printNfTerms fname xs = do
  f <- openFile ("lams/" ++ fname ++ ".lam") WriteMode
  fnf <- openFile ("lams/" ++ fname ++ ".nf.lam") WriteMode
  forM_ xs $ \x -> do
    hPutStrLn f ("-- numSubsts:  " ++ show (suite_numSubsts x))
    hPutStrLn f ("-- bind depth: " ++ show (suite_bindDepth x))
    hPutStrLn f ("-- depth:      " ++ show (suite_depth x))
    hPrint f (suite_before x)
  forM_ xs $ \x ->
    hPrint fnf (suite_after x)

readNfTerms :: String -> IO [NfTerm]
readNfTerms fname =
  do
    f <- readFile ("lams/" ++ fname ++ ".lam")
    fnf <- readFile ("lams/" ++ fname ++ ".nf.lam")
    let loop (ss : bd : dp : lam : xs) (nlam : ys)
          | Just ss_str <- List.stripPrefix "-- numSubsts:  " ss,
            Just bd_str <- List.stripPrefix "-- bind depth: " bd,
            Just dp_str <- List.stripPrefix "-- depth:      " dp =
            NfTerm
              { suite_before = read lam,
                suite_after = read nlam,
                suite_numSubsts = read ss_str,
                suite_bindDepth = read bd_str,
                suite_depth = read dp_str
              } :
            loop xs ys
        loop (x : xs) (y : ys) = error ("cannot parse " ++ x)
        loop [] [] = []
        loop _ _ = error "nf file doesn't match input"
    return $ loop (lines f) (lines fnf)

-- | Add stats to the source
-- and create the nf file
addNf :: String -> IO ()
addNf str = do
  lams2 <- readLams str
  nfs <- nfTerms lams2
  printNfTerms str nfs

readNfPrint :: String -> IO ()
readNfPrint str = do
  lams <- readLams str
  nfs <- nfTerms lams
  printNfTerms str nfs