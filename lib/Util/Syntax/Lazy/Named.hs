-- | The Uses the lazy LC syntax, but specialized to IdInt
-- A simple, named representation of lambda terms
module Util.Syntax.Lazy.Named where

import Data.List (union, (\\))
import qualified Text.ParserCombinators.ReadP as RP
import qualified Text.PrettyPrint.HughesPJ as PP
import Util.IdInt
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Imports
import Util.Syntax.Lazy.Lambda hiding (allVars, freeVars)

type Term = LC IdInt

-- Compute the free variables of an expression.

freeVars :: Term -> S.IdIntSet
freeVars (Var v) = S.singleton v
freeVars (Lam v e) = freeVars e S.\\ S.singleton v
freeVars (App f a) = freeVars f `S.union` freeVars a

-- Compute *all* variables in an expression.

allVars :: Term -> S.IdIntSet
allVars (Var v) = S.singleton v
allVars (Lam _ e) = allVars e
allVars (App f a) = allVars f `S.union` allVars a

-- For alpha-equivalence, we can optimize the case where the binding variable is
-- the same. However, if it is not, we need to check to see if the left binding
-- variable is free in the body of the right Lam. If so, then the terms cannot be
-- alpha-equal. Otherwise, we can remember that the right one matches up with the
-- left.

applyPermLC :: Perm IdInt -> Term -> Term
applyPermLC m (Var x) = Var (applyPerm m x)
applyPermLC m (Lam x e) = Lam (applyPerm m x) (applyPermLC m e)
applyPermLC m (App t u) = App (applyPermLC m t) (applyPermLC m u)

-- inefficient version
aeq :: Term -> Term -> Bool
aeq = aeqd
  where
    aeqd (Var v1) (Var v2) = v1 == v2
    aeqd (Lam v1 e1) (Lam v2 e2)
      | v1 == v2 = aeqd e1 e2
      | v1 `S.member` freeVars (Lam v2 e2) = False
      | otherwise = aeqd e1 (applyPermLC p e2)
      where
        p = (extendPerm emptyPerm v1 v2)
    aeqd (App a1 a2) (App b1 b2) =
      aeqd a1 b1 && aeqd a2 b2
    aeqd _ _ = False

---------------------------- Read/Show -------------------------------------
