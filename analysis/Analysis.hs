module Analysis where

import System.IO (hGetLine, hPutStrLn, IOMode(..), withFile)
import System.Directory
import System.FilePath
import Control.Monad
import qualified Data.List as List
import qualified Data.Maybe as Maybe

directory = "../results/constructed/"
benchmark = "adjust"
iterations = 20

outputFile = "../" ++ benchmark ++ "-all.csv"

dirs = ["DeBruijn/" , "DeBruijn/Par/"
       , "DeBruijn/Lazy/", "DeBruijn/Lazy/"
       , "LocallyNameless/", "Named/" ]


isCSV f = ext == ".csv" && ("-" ++ benchmark) `List.isSuffixOf` name where
  (name, ext) = splitExtension f

getData :: FilePath -> IO [Double]
getData f = withFile f ReadMode $ \h -> do
    header <- hGetLine h
    values <- forM [1 .. iterations] $ \i -> do
       line <- hGetLine h
       let rest = tail (dropWhile (/= ',') line)
       let str = takeWhile (/= ',') rest
       return (read str :: Double)
    return values   

printCSV :: [FilePath] -> [[Double]] -> IO ()
printCSV files vss = withFile outputFile WriteMode $ \h -> do
  let shorten file = Maybe.fromJust (List.stripPrefix directory file)
  hPutStrLn h $ concat (List.intersperse "," (map shorten files))
  forM_ [0 .. (iterations-1)] $ \i -> do
    let vals = map (\vs -> vs !! i) vss 
    hPutStrLn h $ concat (List.intersperse "," (map show vals))
  
makeCSV :: IO ()
makeCSV = do
  d <- getCurrentDirectory
  putStrLn $ "Current directory is: " ++ d
  files <- forM dirs $ \d -> do
    files <- listDirectory $ directory ++ d
    return $ map ((directory ++ d) ++) files
  let all_csv_files = List.nub (filter isCSV (concat files))
  vss <- forM all_csv_files getData
  printCSV all_csv_files vss
  
    
  


