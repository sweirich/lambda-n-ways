module Util.Impl where

{-
Every lambda calculus implementation must have a way to convert to and from
a "named" representation, a way to compute the normal form, and a way
to determine alpha-equivalence.  For uniformity, we package these components up
in a data structure.
-}

import Control.Monad.State
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Util.Id
import Util.IdInt
import Util.IdInt.Set (IdIntSet)
import qualified Util.IdInt.Set as IdIntSet
import Util.Imports
import qualified Util.Misc as Misc
import qualified Util.Stats as Stats
import Util.Syntax.Lambda
import Prelude hiding (abs)
import GHC.Stack

data LambdaImpl = forall a.
  NFData a =>
  LambdaImpl
  { impl_name :: String,
    impl_fromLC :: LC IdInt -> a,
    impl_toLC :: a -> LC IdInt,
    impl_nf :: a -> a,
    impl_nfi :: Int -> a -> Stats.M a,
    impl_eval :: a -> a,
    impl_aeq :: a -> a -> Bool
  }


---------------------------------------------------------
---------------------------------------------------------

toIdInt :: (Ord v) => LC v -> LC IdInt
toIdInt e = evalState (conv e) (0, fvmap)
  where
    fvmap =
      Prelude.foldr
        (\(v, i) m -> M.insert v (IdInt i) m)
        M.empty
        (zip (S.toList (Util.Syntax.Lambda.freeVars e)) [1 ..])

    conv :: (Ord v) => LC v -> FreshM v (LC IdInt)
    conv (Var v) = Var <$> convVar v
    conv (Lam v e0) = Lam <$> convVar v <*> conv e0
    conv (App f a) = App <$> conv f <*> conv a
    conv (Bool b) = return (Bool b)
    conv (If a b c) = If <$> conv a <*> conv b <*> conv c

-- | Read a single term from a file
getTerm :: String -> IO (LC IdInt)
getTerm filename = do
  contents <- readFile filename
  let s = Misc.stripComments contents
  return $ toIdInt ((read :: String -> LC Id) s)

-- | Read a list of terms from a file
getTerms :: String -> IO [LC IdInt]
getTerms filename = do
  contents <- readFile filename
  let ss = filter (/= "") (lines (Misc.stripComments contents))
  return $ map (toIdInt . (read :: String -> LC Id)) ss

lambdaTrue :: LC IdInt
lambdaTrue = Lam (IdInt 0) (Lam (IdInt 1) (Var (IdInt 0)))

lambdaFalse :: LC IdInt
lambdaFalse = Lam (IdInt 0) (Lam (IdInt 1) (Var (IdInt 1)))