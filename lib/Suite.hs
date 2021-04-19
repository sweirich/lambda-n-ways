module Suite where

--import Impl.NominalG

-- import Impl.DeBruijnC

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
import Impl.Simple
import qualified Impl.SimpleB
import qualified Impl.SimpleH
import qualified Impl.SimpleM
import Impl.Unbound
import Impl.UnboundGenerics
import Impl.Unique
import Imports
import Lambda
import qualified LocallyNameless.Opt
import qualified LocallyNameless.Ott
import qualified LocallyNameless.Par
import qualified LocallyNameless.ParOpt
import qualified LocallyNameless.Typed
import qualified LocallyNameless.TypedOpt
import qualified Misc

impls :: [LambdaImpl]
impls =
  [ --Impl.HOAS.impl,
    -- LocallyNameless.Opt.impl,
    -- LocallyNameless.TypedOpt.impl,
    -- Impl.DeBruijn.impl,
    -- DeBruijnPar.F.impl,
    -- DeBruijnPar.FB.impl,
    -- DeBruijnPar.L.impl,
    -- DeBruijnPar.P.impl
    -- DeBruijnPar.Scoped.impl,
    -- DeBruijnPar.B.impl,
    -- Impl.Kit.impl,
    -- Impl.BoundDB.impl
    -- LocallyNameless.Ott.impl,
    -- LocallyNameless.Par.impl,
    -- LocallyNameless.ParOpt.impl,
    -- LocallyNameless.Typed.impl,
    --Impl.SimpleH.impl
    Impl.SimpleB.impl
    --Impl.SimpleM.impl
    --Impl.Simple.impl
    --Impl.UnboundGenerics.impl
    -- Impl.Unbound.impl
    -- Impl.Unique.impl
    -- Core.Nf.impl,
    -- Impl.NominalG.impl -- generally too slow (12s vs. <200 ms for everything else)
  ]

-- Convert a lambda-calculus to

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
    conv (Lam v e) = Lam <$> convVar v <*> conv e
    conv (App f a) = App <$> conv f <*> conv a

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

{-
-- Convenience functions for creating test cases
infixl 5 @@

(@@) :: LC IdInt -> LC IdInt -> LC IdInt
a @@ b = App a b

lam :: Int -> LC IdInt -> LC IdInt
lam i = Lam (IdInt i)

var :: Int -> LC IdInt
var i = Var (IdInt i)
-}

lambdaTrue :: LC IdInt
lambdaTrue = Lam (IdInt 0) (Lam (IdInt 1) (Var (IdInt 0)))

lambdaFalse :: LC IdInt
lambdaFalse = Lam (IdInt 0) (Lam (IdInt 1) (Var (IdInt 1)))
