module Suite where

--import Impl.NominalG

-- import Impl.DeBruijnC

import Control.Monad.State (evalState)
import Core.Nf
import qualified Data.Map.Strict as M
import DeBruijn.Bound
import DeBruijn.Kit
import DeBruijn.Lennart
import DeBruijn.Par.B
import DeBruijn.Par.F
import DeBruijn.Par.FB
import DeBruijn.Par.L
import DeBruijn.Par.P
import DeBruijn.Par.Scoped
import Id
import IdInt
import Impl
import Imports
import Lambda
import Lennart.HOAS
import Lennart.Simple
import Lennart.Unique
import qualified LocallyNameless.Opt
import qualified LocallyNameless.Ott
import qualified LocallyNameless.Par
import qualified LocallyNameless.ParOpt
import qualified LocallyNameless.Typed
import qualified LocallyNameless.TypedOpt
import LocallyNameless.Unbound
import LocallyNameless.UnboundGenerics
import qualified Misc
--import qualified Named.Nom as Nom
import qualified Named.NominalG as NominalG
import qualified Named.SimpleB as SimpleB
import qualified Named.SimpleH as SimpleH
import qualified Named.SimpleM as SimpleM

impls :: [LambdaImpl]
impls =
  [ --Lennart.HOAS.impl,
    DeBruijn.Lennart.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Kit.impl
    --DeBruijn.Bound.impl,
    --LocallyNameless.Opt.impl,
    --LocallyNameless.ParOpt.impl,
    --SimpleM.impl
    --LocallyNameless.UnboundGenerics.impl
    -- LocallyNameless.Unbound.impl
  ]

{- Lennart.HOAS.impl,
LocallyNameless.Opt.impl,
LocallyNameless.TypedOpt.impl,
Lennart.DeBruijn.impl,
DeBruijn.Par.F.impl,
DeBruijn.Par.FB.impl,
DeBruijn.Par.L.impl,
DeBruijn.Par.P.impl, -}
--DeBruijn.Par.Scoped.impl
{- DeBruijn.Par.B.impl,
DeBruijn.Kit.impl,
DeBruijn.Bound.impl,
LocallyNameless.Opt.impl,
LocallyNameless.Par.impl,
LocallyNameless.ParOpt.impl,
LocallyNameless.Typed.impl,
SimpleH.impl,
SimpleB.impl -- BROKEN
SimpleM.impl,
Lennart.Simple.impl,
Lennart.Unique.impl,
Core.Nf.impl, -}
-- Named.NominalG.impl -- generally too slow (12s vs. <200 ms for everything else)

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
