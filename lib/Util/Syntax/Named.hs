-- | A simple, named, strict representation of lambda terms
-- Uses IdInts for variables
module Util.Syntax.Named where

import Data.List (union, (\\))
import qualified Text.ParserCombinators.ReadP as RP
import qualified Text.PrettyPrint.HughesPJ as PP
import Util.IdInt
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Imports
import qualified Util.Syntax.Lambda as LC

data Term = Var {-# UNPACK #-} !IdInt 
     | Lam {-# UNPACK #-} !IdInt !Term | App !Term !Term
     | Bool {-# UNPACK #-} !Bool | If !Term !Term !Term
  deriving (Eq, Generic)

instance NFData Term

fromLC :: LC.LC IdInt -> Term
fromLC (LC.Var v) = Var v
fromLC (LC.Lam v e) = Lam v (fromLC e)
fromLC (LC.App a b) = App (fromLC a) (fromLC b)
fromLC (LC.Bool b) = Bool b
fromLC (LC.If a b c) = If (fromLC a) (fromLC b) (fromLC c)

toLC :: Term -> LC.LC IdInt
toLC (Var v) = LC.Var v
toLC (Lam v e) = LC.Lam v (toLC e)
toLC (App a b) = LC.App (toLC a) (toLC b)
toLC (Bool b) = LC.Bool b
toLC (If a b c) = LC.If (toLC a) (toLC b) (toLC c)

-- Compute the free variables of an expression.

freeVars :: Term -> S.IdIntSet
freeVars (Var v) = S.singleton v
freeVars (Lam v e) = freeVars e S.\\ S.singleton v
freeVars (App f a) = freeVars f `S.union` freeVars a
freeVars (Bool b) = S.empty
freeVars (If a b1 b2) =
  freeVars a `S.union` freeVars b1 `S.union`
  freeVars b2
-- Compute *all* variables in an expression.

allVars :: Term -> S.IdIntSet
allVars (Var v) = S.singleton v
allVars (Lam _ e) = allVars e
allVars (App f a) = allVars f `S.union` allVars a
allVars (Bool b) = S.empty
allVars (If a b1 b2) =
  allVars a `S.union` allVars b1 `S.union`
  allVars b2

-- For alpha-equivalence, we can optimize the case where the binding variable is
-- the same. However, if it is not, we need to check to see if the left binding
-- variable is free in the body of the right Lam. If so, then the terms cannot be
-- alpha-equal. Otherwise, we can remember that the right one matches up with the
-- left.

applyPermLC :: LC.Perm IdInt -> Term -> Term
applyPermLC m (Var x) = Var (LC.applyPerm m x)
applyPermLC m (Lam x e) = Lam (LC.applyPerm m x) (applyPermLC m e)
applyPermLC m (App t u) = App (applyPermLC m t) (applyPermLC m u)
applyPermLC m (Bool b) = Bool b
applyPermLC m (If a b c) = If (applyPermLC m a) (applyPermLC m b)
   (applyPermLC m c)
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
        p = LC.extendPerm LC.emptyPerm v1 v2
    aeqd (App a1 a2) (App b1 b2) =
      aeqd a1 b1 && aeqd a2 b2
    aeqd (Bool b1) (Bool b2) = b1 == b2
    aeqd (If a1 b1 c1) (If a2 b2 c2) =
      aeqd a1 a2 && aeqd b1 b2 && aeqd c1 c2
    aeqd _ _ = False
