module Util.Misc (stripComments, nonblankLines, interactArgs) where

import System.Environment (getArgs)

-- | eliminate Haskell like '--' comments from the complete
-- string of a source file
stripComments :: String -> String
stripComments "" = ""
stripComments ('-' : '-' : cs) = skip cs
  where
    skip "" = ""
    skip s@('\r' : '\n' : _) = stripComments s
    skip s@('\n' : _) = stripComments s
    skip (_ : s) = skip s
stripComments (c : cs) = c : stripComments cs

nonblankLines :: String -> [String]
nonblankLines s = filter (/= "") (lines s)

-- | Like `interact', but also pass program arguments.
interactArgs :: ([String] -> String -> String) -> IO ()
interactArgs f = do
  args <- getArgs
  interact (f args)
