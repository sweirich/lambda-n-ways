{-# LANGUAGE TypeApplications #-}

module Impl where

{-
Every lambda calculus implementation must have a way to convert to and from
a "named" representation, a way to compute the normal form, and a way
to determine alpha-equivalence.  For uniformity, we package these components up
in a data structure.
-}

import Control.Monad.State
import qualified Data.Map.Strict as M
import Id
import IdInt
import Imports
import Lambda
import Misc
import Prelude hiding (abs)

data LambdaImpl = forall a.
  NFData a =>
  LambdaImpl
  { impl_name :: String,
    impl_fromLC :: LC IdInt -> a,
    impl_toLC :: a -> LC IdInt,
    impl_nf :: a -> a,
    impl_nfi :: Int -> a -> Maybe a,
    impl_aeq :: a -> a -> Bool
    --           impl_fvs    :: a -> IdIntSet,
    --           impl_subst  :: a -> IdInt -> a -> a
  }

{-
unabs :: A.LC IdInt -> LC IdInt
unabs (A.Var x) = Var x
unabs (A.Lam bnd) = let (x, a) = A.unbind' bnd in Lam x (unabs a)
unabs (A.App a b) = App (unabs a) (unabs b)

abs :: LC IdInt -> A.LC IdInt
abs (Var x) = A.Var x
abs (Lam x a) = A.lam' x (abs a)
abs (App a b) = A.App (abs a) (abs b)

fromBindingImpl :: forall v. A.BindingImpl v => Proxy v -> String -> LambdaImpl
fromBindingImpl _ name =
  LambdaImpl
    { impl_name = name,
      impl_fromLC = A.runBindM @v . A.fromLC . abs,
      impl_toLC = A.runBindM @v . fmap unabs . A.toLC,
      impl_nf = A.nf @v,
      impl_nfi = A.instrNormalize,
      impl_aeq = \x y -> A.runBindM @v (A.aeq x y)
    }
-}

---------------------------------------------------------
---------------------------------------------------------

toIdInt :: (Ord v) => LC v -> LC IdInt
toIdInt e = evalState (conv e) (0, fvmap)
  where
    fvmap =
      Prelude.foldr
        (\(v, i) m -> M.insert v (IdInt i) m)
        M.empty
        (zip (Lambda.freeVars e) [1 ..])

    conv :: (Ord v) => LC v -> FreshM v (LC IdInt)
    conv (Var v) = Var <$> convVar v
    conv (Lam v e0) = Lam <$> convVar v <*> conv e0
    conv (App f a) = App <$> conv f <*> conv a

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