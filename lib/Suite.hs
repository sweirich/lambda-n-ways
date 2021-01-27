module Suite where

--import Impl.NominalG

-- import Impl.DeBruijnC

import Core.Nf
import DeBruijnPar.B
import DeBruijnPar.F
import DeBruijnPar.FB
import DeBruijnPar.L
import DeBruijnPar.P
import DeBruijnPar.Scoped
import IdInt
import Impl
import Impl.BoundDB
import Impl.DeBruijn
import Impl.HOAS
import Impl.Kit
import Impl.Simple
import Impl.SimpleB
import Impl.Unbound
import Impl.UnboundGenerics
import Impl.Unique
import Lambda
import qualified Misc
import Test.QuickCheck

impls :: [LambdaImpl]
impls =
  [ DeBruijnPar.F.impl,
    DeBruijnPar.FB.impl,
    DeBruijnPar.L.impl,
    DeBruijnPar.P.impl,
    DeBruijnPar.B.impl,
    DeBruijnPar.Scoped.impl,
    Impl.DeBruijn.impl,
    Impl.BoundDB.impl,
    Impl.HOAS.impl,
    Impl.Kit.impl,
    Impl.SimpleB.impl,
    Impl.Simple.impl,
    Impl.UnboundGenerics.impl,
    Impl.Unbound.impl,
    Impl.Unique.impl,
    Core.Nf.impl
    -- , Impl.NominalG.impl -- generally too slow (12s vs. <200 ms for everything else)
  ]

--------------------------------------------------------------
--------------------------------------------------------------

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

-- Convenience functions for creating test cases
infixl 5 @@

(@@) :: LC IdInt -> LC IdInt -> LC IdInt
a @@ b = App a b

lam :: Int -> LC IdInt -> LC IdInt
lam i = Lam (IdInt i)

var :: Int -> LC IdInt
var i = Var (IdInt i)

lambdaTrue :: LC IdInt
lambdaTrue = lam 0 (lam 1 (var 0))

lambdaFalse :: LC IdInt
lambdaFalse = lam 0 (lam 1 (var 1))

{-
-- | Ok if either times out too early. But if they both finish, it should
-- be with the same answer
eqMaybe :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Property
eqMaybe f (Just x) (Just y) = classify True "aeq" (f x y)
eqMaybe _f _ _ = property True

prop_sameNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Int -> LC IdInt ->  Property
prop_sameNF f i x = eqMaybe Lambda.aeq (Simple.nfi i x) (f i x)

lc_nfi :: LambdaImpl -> Int -> LC IdInt -> Maybe (LC IdInt)
lc_nfi LambdaImpl{..} i x =
  impl_toLC <$>  impl_nfi i (impl_fromLC x)

-- NOTE: need "fueled" version of normalization
-- NOTE: hard to shrink and stay well-closed
prop_closedNF :: LambdaImpl -> Property
prop_closedNF impl = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
      eqMaybe Unique.aeq (lc_nfi DeBruijn.impl 1000 x) (lc_nfi impl 1000 x)
-}
