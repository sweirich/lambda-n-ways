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
import qualified Named.Lazy.Simple as Simple
import qualified Named.Unique as Unique
import Suite
import System.IO
import Test.QuickCheck
import Util.Id
import Util.IdInt
import Util.Impl
import Util.Misc
import Util.Syntax.Lambda

import Control.Exception

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

-- stats for random15.lam
-- sz: 10
{-
> median $ map mean ((map . map) subst_occ (map suite_substStats nfts))
1.411764705882353
   num substs: 15 15 15 15 15 16 16 16 16 16 16 16 17 17 17 17 18 18 18 19 19 19 19 19 20 20 20 21 21 21 21 21 21 21 22 22 22 22 22 23 23 24 24 24 24 24 25 25 25 25 25 25 26 27 27 28 28 29 29 30 30 30 30 30 30 31 31 31 32 32 32 33 33 35 36 36 37 41 43 44 45 46 46 47 50 51 56 56 59 60 68 70 74 79 79 93 95 112 157 158
   bind depths: 12 12 13 14 15 15 16 16 16 17 17 17 17 17 17 17 17 17 18 19 19 19 19 19 19 20 20 20 20 21 21 21 21 21 22 22 22 22 22 23 24 24 24 24 25 25 25 25 25 25 26 26 27 27 27 27 28 28 28 29 29 29 29 29 29 29 30 30 31 31 31 32 32 32 32 33 33 33 33 33 34 34 35 35 35 36 36 36 37 37 38 39 39 40 40 40 46 46 49 52
   depth:       19 21 23 26 28 28 29 29 29 30 30 30 30 30 30 31 31 31 31 32 32 32 34 35 35 35 35 37 37 37 38 39 39 40 40 41 41 42 42 43 43 43 45 45 45 46 46 46 46 47 48 48 49 49 49 50 51 52 52 52 53 53 54 55 55 55 55 56 56 57 59 59 59 60 60 61 61 61 62 62 63 63 63 64 65 65 69 69 69 69 70 70 73 74 75 75 86 90 93 95
-}

-- stats for random16.lam
-- sz: 10
-- > median $ map mean ((map . map) subst_occ (map suite_substStats nfts))
-- 1.457142857142857
{-
  num substs: 16 16 16 16 17 17 17 17 17 17 17 17 18 18 18 18 18 18 18 18 19 19 19 19 20 20 20 20 20 20 20 21 21 21 21 22 22 22 22 23 23 23 24 24 25 25 26 26 29 30 30 30 30 31 32 32 33 34 34 34 35 35 35 35 35 37 38 41 41 41 43 43 43 43 44 45 46 48 49 49 49 50 53 56 56 56 63 65 66 67 68 69 70 83 92 95 96 98 115 147
   bind depths: 14 14 15 15 15 16 16 16 16 17 17 17 17 17 17 17 17 18 18 18 19 19 19 19 19 20 21 21 21 22 22 22 22 22 22 23 23 23 24 24 24 24 24 24 24 24 25 25 25 26 26 26 26 26 27 27 27 27 27 27 28 29 29 29 29 30 30 31 31 31 32 32 33 33 33 33 34 34 35 35 36 36 36 36 36 36 38 39 39 39 40 40 40 41 41 46 47 49 54 57
   depth:       25 26 26 29 29 29 30 30 30 30 31 31 31 32 32 32 32 32 32 33 33 34 34 35 35 36 36 36 37 39 39 40 40 40 41 41 42 42 42 43 43 43 43 43 43 44 45 45 45 45 45 46 46 48 49 49 49 49 50 51 52 53 53 54 54 54 56 57 58 58 59 59 60 60 60 61 63 65 65 66 66 66 67 67 67 68 70 72 72 73 76 76 77 77 79 84 84 93 95 105
-}

-- stats for random17.lam
-- sz: 10
-- > median $ map mean ((map . map) subst_occ (map suite_substStats nfts))
-- 1.3333333333333333
{-
  num substs: 17 17 17 17 17 17 17 18 18 18 18 18 18 18 19 19 19 20 20 20 20 20 20 22 22 22 23 23 23 24 24 24 24 25 25 26 26 26 26 26 26 27 27 28 29 29 29 29 29 29 30 31 32 32 33 33 33 33 34 34 35 35 35 35 36 36 38 38 39 39 40 41 41 42 43 44 45 45 48 48 49 49 51 54 55 56 60 62 70 75 75 79 90 93 93 97 101 114 123 140
   bind depths: 12 13 13 14 14 14 15 15 16 16 17 17 17 18 18 18 18 19 19 19 20 20 20 21 22 22 22 22 22 23 23 23 23 23 23 24 24 24 24 24 24 25 25 25 25 25 26 26 26 26 26 27 27 28 28 29 29 30 30 30 31 31 31 31 31 31 32 32 32 32 33 33 33 34 34 34 34 34 34 34 35 35 35 35 37 37 38 39 40 40 41 41 41 42 45 46 46 47 47 48
   depth:       19 24 24 25 25 25 27 27 28 30 31 31 31 32 32 33 35 36 37 37 37 37 38 39 39 39 40 40 41 41 41 42 43 43 43 43 43 43 43 44 45 45 46 46 46 47 48 48 49 49 50 50 50 51 51 51 51 52 53 55 57 57 58 58 59 60 61 61 61 61 61 62 62 62 62 62 62 62 62 62 63 66 66 67 68 69 69 71 72 75 76 77 78 78 80 84 85 87 90 91
   -}

-- stats for random18.lam
{-
sz: 10
   num substs: 18 18 18 18 18 18 19 20 20 20 20 20 21 21 21 21 22 22 22 22 23 23 23 23 24 24 25 25 26 26 26 26 26 26 26 26 27 27 27 27 27 28 28 28 28 29 29 30 30 30 30 31 31 31 31 32 33 33 33 33 34 34 34 34 35 35 36 36 36 36 37 38 38 39 39 39 40 42 44 44 44 45 45 50 51 56 56 63 66 69 71 71 74 76 76 84 86 88 143 156
   bind depths: 13 14 16 16 17 17 17 17 17 17 17 18 18 18 19 19 20 20 20 20 20 20 21 21 21 21 21 21 22 22 22 22 22 23 23 23 23 23 23 24 24 25 25 25 25 26 27 27 27 27 27 27 27 28 28 28 28 28 29 29 30 30 30 30 30 30 31 31 31 31 32 32 32 32 32 32 33 33 33 34 34 35 35 36 36 37 38 38 38 38 39 39 40 41 42 42 42 42 49 50
   depth:       22 25 26 29 29 30 30 30 30 31 32 33 34 34 35 35 36 36 36 38 38 38 39 39 39 39 40 40 40 40 41 41 42 42 42 42 42 42 43 43 43 44 46 46 47 47 48 49 50 51 51 52 52 52 52 52 53 53 53 53 54 55 55 55 56 56 56 57 57 57 57 58 58 58 60 60 61 61 61 63 64 65 66 66 66 67 68 69 71 73 73 73 73 73 75 75 76 77 90 91
> median $ map mean ((map . map) subst_occ (map suite_substStats nfts))
1.3548387096774193
-}

-- stats for random19.lam
{-
sz: 10
   num substs: 19 19 19 19 19 19 20 20 21 21 21 21 21 22 22 23 23 23 23 23 23 23 23 24 24 24 24 25 25 25 25 25 25 25 26 26 26 26 26 27 27 27 27 27 27 29 30 30 30 31 31 32 33 33 33 33 33 33 33 34 34 34 34 35 36 36 36 37 37 39 39 40 43 45 46 48 48 48 49 50 52 52 52 53 57 57 59 60 61 63 63 67 70 71 80 83 90 91 91 120
   bind depths: 15 17 17 17 17 17 17 17 17 18 18 18 19 19 19 19 19 19 19 20 20 20 20 21 21 21 21 21 21 21 22 22 22 22 22 22 22 23 23 24 24 24 24 25 25 26 26 27 27 27 27 27 27 27 28 28 28 28 28 28 28 29 30 30 30 30 30 30 30 31 31 31 32 32 32 32 33 33 34 34 34 35 35 35 35 36 36 36 36 38 38 38 39 40 41 41 42 43 45 45
   depth:       29 29 30 30 31 31 31 31 31 32 32 32 32 33 33 34 35 35 35 35 35 37 37 37 38 38 39 39 39 39 39 39 40 41 41 42 42 43 43 43 43 43 43 44 44 47 47 48 48 49 49 49 49 49 50 50 50 51 51 52 53 54 54 54 54 54 54 54 54 55 56 56 56 56 57 61 61 62 64 65 65 65 65 66 66 67 67 68 69 71 71 74 74 74 75 75 78 79 84 85
> median $ map mean ((map . map) subst_occ (map suite_substStats nfts))
1.2375
-}

-- stats for random20.lam
{-
  sz: 10
   num substs: 20 20 20 20 20 20 20 20 20 20 20 20 20 21 21 21 21 21 21 21 21 21 22 22 22 22 23 23 23 23 23 23 23 24 24 24 24 25 25 25 25 25 25 25 25 25 26 26 26 26 27 27 28 28 29 29 29 30 30 31 32 33 34 34 35 35 35 35 36 37 37 38 39 39 40 41 41 41 42 44 47 51 52 54 54 54 54 55 58 58 60 66 69 71 72 75 80 81 103 112
   bind depths: 13 15 16 16 16 17 17 17 17 17 17 17 17 18 18 18 18 18 18 19 19 19 19 19 19 19 19 19 20 20 21 21 21 21 22 22 22 22 22 22 23 23 23 23 24 24 24 24 25 25 25 25 26 26 26 27 27 27 27 28 29 29 30 31 31 31 31 31 31 32 32 33 33 33 33 33 34 35 35 35 35 35 36 36 36 37 37 38 39 40 41 41 42 44 45 47 47 50 57 58
   depth:       22 27 29 29 30 30 31 31 31 31 31 31 31 32 32 32 32 33 33 33 34 34 34 34 35 35 35 36 36 37 37 38 39 39 39 39 40 40 40 41 41 42 43 43 43 43 43 44 44 44 45 45 45 47 48 49 50 51 51 53 54 56 56 57 57 58 59 60 60 60 60 60 61 61 61 61 61 62 64 65 66 66 67 67 68 68 69 72 73 75 76 78 79 82 82 90 90 95 102 106
> median $ map mean ((map . map) subst_occ (map suite_substStats nfts))
1.4318181818181819
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
            putStrLn $ "   num substs: " ++ show (length (Simple.substStats ss))
            putStrLn $ "   subst " ++ Simple.show_stats (Simple.substStats ss)
          Nothing -> do
            putStrLn $ "   failed for:        " ++ show n
            loop (n * 2)
  loop 1000

-- calculate stats for a file of terms

-- | Statistics about normalization procedure for terms
data NfTerm = NfTerm
  { suite_before :: LC IdInt,
    suite_after :: LC IdInt,
    suite_numSubsts :: Int,
    suite_bindDepth :: Int,
    suite_depth :: Int,
    suite_substStats :: [Simple.SubstStat]
  }


readLams :: String -> IO [LC IdInt]
readLams fname = do
  contents <- readFile $ "lams/" ++ fname ++ ".lam"
  return $ map parse (nonblankLines (stripComments contents))
  where
    parse :: String -> LC IdInt
    parse s = toIdInt (read s :: LC Id)

type Reducer = Int -> LC IdInt -> Maybe (LC IdInt, Simple.St)

-- Apply a reduction function to a list of lambda calculus terms, 
-- producing a normal form. Only return results if there is a difference
-- after reduction
nfTerms :: Reducer -> [LC IdInt] -> IO [NfTerm]
nfTerms reduce tms = do
  forM tms $ \tm -> do
    let stm = Scoped.toDB tm
    case reduce 200000 tm of
      Just (tm', ss) ->
        if not (tm `Util.Syntax.Lambda.aeq` tm')
          then do
            return $
              NfTerm
                { suite_before = tm,
                  suite_after = tm',
                  suite_numSubsts = length (Simple.substStats ss),
                  suite_bindDepth = maxBindingDepth tm,
                  suite_depth = depth tm,
                  suite_substStats = Simple.substStats ss
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
      tm <- generate (resize sz (genScopedRed :: Gen (LC IdInt)))
      case Simple.iNf 2000 tm of
        Just (tm', ss) ->
          if length (Simple.substStats ss) >= 20
            then do
              putStrLn $ "Generation:" ++ show n
              let x =
                    NfTerm
                      { suite_before = tm,
                        suite_after = tm',
                        suite_numSubsts = length (Simple.substStats ss),
                        suite_bindDepth = maxBindingDepth tm,
                        suite_depth = depth tm,
                        suite_substStats = Simple.substStats ss
                      }
              loop (n -1) (x : tms)
            else loop n tms
        Nothing -> loop n tms

median :: (Ord a, Num a) => [a] -> a
median xs = List.sort xs !! (n `div` 2) where n = length xs

printNfTerms :: String -> String -> [NfTerm] -> IO ()
printNfTerms fname ext xs = do
  -- f <- openFile ("lams/" ++ fname ++ ".lam") WriteMode
  fnf <- openFile (fname ++ ext ++ ".lam") WriteMode
  -- forM_ xs $ \x -> do  
  --  hPrint f (suite_before x)
  forM_ xs $ \x -> do
    hPutStrLn fnf ("-- numSubsts:  " ++ show (suite_numSubsts x))
    hPutStrLn fnf ("-- bind depth: " ++ show (suite_bindDepth x))
    hPutStrLn fnf ("-- depth:      " ++ show (suite_depth x))
    hPutStrLn fnf ("-- substs:     " ++ Simple.show_stats (suite_substStats x))
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
                suite_depth = read dp_str,
                suite_substStats = []
              } :
            loop xs ys
        loop (x : xs) (y : ys) = error ("cannot parse " ++ x)
        loop [] [] = []
        loop _ _ = error "nf file doesn't match input"
    return $ loop (lines f) (lines fnf)

-- | Add stats to the source
-- and create the nf file
addNfs :: String -> IO ()
addNfs str = do
  lams <- readLams str
  nfs <- nfTerms Simple.iNf lams
  printNfTerms str ".nf" nfs

addNf :: String -> IO ()
addNf str = do
  lam <- getTerm str
  nfs <- nfTerms Simple.iNf [lam]
  printNfTerms str ".nf" nfs

addEvals :: String -> IO ()
addEvals str = do
  lams <- readLams str
  evs <- nfTerms Simple.iEval lams
  printNfTerms str ".eval" evs

addEval :: String -> IO ()
addEval str = do
  lams <- getTerm ("lambs/" ++ str ++ ".lam")
  evs <- nfTerms Simple.iEval [lams]
  printNfTerms ("lambs/" ++ str) ".eval" evs

-- >>> :t try
-- try :: Exception e => IO a -> IO (Either e a)

-- >>> :t filterM
-- filterM :: Applicative m => (a -> m Bool) -> [a] -> m [a]

lam_files = ["adjust","capture10","constructed","constructed10","constructed20","fact5",
  "foursubst","full","full-2","id","lams100","lazy","lennart","lennartchurch","onesubst",
  "random","random15","random16","random17","random18","random19","random2","random20",
  "random25","random25-19","random25-20","random35","regression1","simple",
  "t1","t2","t3","t4","t5","t6","t7","tests","threesubst","twosubst"]


addAllEvals :: [String] -> IO ()
addAllEvals files = do
  let f s = do 
              x <- try @SomeException (addEvals s)
              putStr (s ++ ": ")
              case x of 
                Left _ -> do x <- try @SomeException (addEval s)
                             case x of 
                              Left _ -> return False
                              Right _ -> return True
                Right () -> return True
  _ <- filterM f files
  return ()
