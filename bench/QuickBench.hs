-- | Generate a benchmark suite for normalization
-- 
-- Goal is to generate random sets of terms that 
module QuickBench where

import qualified Data.List as List
import Misc
import Lambda
import IdInt
import Impl
import Suite
import qualified Simple
import qualified Unique
import Test.QuickCheck

{-
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
  let
    tm :: LC IdInt
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
--mkNfSuite :: Int -> IO [LC IdInt]
mkNfSuite sz = do
    let num = 25
    tms_ss <- loop num []
    let (tms, ss) = List.unzip tms_ss
    putStrLn $ "sz: " ++ show sz
    putStrLn $ "   num substs: " ++ List.intercalate " " (map show (List.sort (map Simple.numSubsts ss)))
    putStrLn $ "   bind depths: " ++ List.intercalate " " (map show (List.sort (map maxBindingDepth tms)))
    putStrLn $ "   depth:       " ++ List.intercalate " " (map show (List.sort (map depth tms)))
    return $ zip tms (zip3 (map Simple.numSubsts ss) (map maxBindingDepth tms) (map depth tms))
  where
    loop 0 tms = return tms
    loop n tms = do
       tm <- generate (resize sz (genScopedLam :: Gen (LC IdInt)))
       case Simple.iNf 1000 tm of
               Just (tm',ss) -> if not (tm `Lambda.aeq` tm') && Simple.numSubsts ss > 25 then loop (n-1) ((tm,ss):tms)
                                else loop n tms
               Nothing -> loop n tms


median :: (Ord a, Num a) => [a] -> a
median xs = List.sort xs !! (n `div` 2) where n = length xs
