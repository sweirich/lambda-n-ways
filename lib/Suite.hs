module Suite where

--import Impl.NominalG

-- import Impl.DeBruijnC

import qualified Abstract.DeBruijn as ADB
import qualified Abstract.DeBruijnPar.B as AB
import qualified Abstract.DeBruijnPar.F as AF
import qualified Abstract.Simple as AS
import qualified Abstract.UnboundGenerics as AUG
import Control.Monad.State (evalState)
import Core.Nf
import qualified Data.Map.Strict as M
import DeBruijnPar.B
import DeBruijnPar.F
import DeBruijnPar.FB
import DeBruijnPar.L
import DeBruijnPar.P
import DeBruijnPar.Scoped
import Id
import IdInt
import Impl
import Impl.BoundDB
import Impl.DeBruijn
import Impl.HOAS
import Impl.Kit
import qualified Impl.LocallyNameless
import qualified Impl.LocallyNamelessOpt
import qualified Impl.LocallyNamelessTyped
import qualified Impl.LocallyNamelessV2
import qualified Impl.LocallyNamelessV3
import Impl.Simple
import Impl.SimpleB
import Impl.Unbound
import Impl.UnboundGenerics
import Impl.Unique
import Imports
import Lambda
import qualified Misc

impls :: [LambdaImpl]
impls =
  [ {- DeBruijnPar.F.impl,
    DeBruijnPar.FB.impl,
    DeBruijnPar.L.impl,
    DeBruijnPar.P.impl,
    DeBruijnPar.B.impl,
    DeBruijnPar.Scoped.impl,
    Impl.DeBruijn.impl,
    Impl.BoundDB.impl,
    Impl.Kit.impl,
    Impl.HOAS.impl,-}
    --Impl.LocallyNameless.impl,
    Impl.LocallyNamelessV2.impl,
    Impl.LocallyNamelessV3.impl
    -- Impl.SimpleB.impl,
    -- Impl.Simple.impl,
    -- Impl.UnboundGenerics.impl,
    -- Impl.Unbound.impl,
    -- Impl.Unique.impl
    -- Core.Nf.impl,
    {- Impl.fromBindingImpl
      (Proxy :: Proxy IdInt)
      "abstract simple",
    Impl.fromBindingImpl
      (Proxy :: Proxy AF.DB)
      "abstract DB_F",
    Impl.fromBindingImpl
      (Proxy :: Proxy AB.DB)
      "abstract DB_B",
    Impl.fromBindingImpl
      (Proxy :: Proxy ADB.DB)
      "abstract DB", -}
    {- Impl.fromBindingImpl
      (Proxy :: Proxy AUG.U)
      "abstract Unbound Generics" -}
    -- , Impl.NominalG.impl -- generally too slow (12s vs. <200 ms for everything else)
  ]

conv :: (Ord v) => LC v -> FreshM v (LC IdInt)
conv (Var v) = Var <$> convVar v
conv (Lam v e) = Lam <$> convVar v <*> conv e
conv (App f a) = App <$> conv f <*> conv a

toIdInt :: (Ord v) => LC v -> LC IdInt
toIdInt e = evalState (conv e) (0, fvmap)
  where
    fvmap =
      Prelude.foldr
        (\(v, i) m -> M.insert v (IdInt i) m)
        M.empty
        (zip (Lambda.freeVars e) [1 ..])

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
