-- Common infrastructure for (strict) implementations with well-scoped
-- DeBruijn indices
-- Datatype definition, equality, NFData instance, conversion to/from named representation
module Util.ScopedDeBruijn where

import Control.DeepSeq
import Data.List (elemIndex)
import Support.Nat
import Text.PrettyPrint.HughesPJ as PP
import Util.IdInt
import Util.Impl
import Util.Imports hiding (from, to)
import Util.Lambda

data Term :: Nat -> Type where
  DVar :: !(Idx g) -> Term g
  DLam :: !(Term ('S g)) -> Term g
  DApp :: !(Term g) -> !(Term g) -> Term g

instance NFData (Term a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

deriving instance Eq (Term n)

toDB :: LC IdInt -> Term 'Z
toDB = to []
  where
    to :: [(IdInt, Idx n)] -> LC IdInt -> Term n
    to vs (Var v) = DVar (fromJust (lookup v vs))
    to vs (Lam v b) = DLam b'
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)

-- Convert back from deBruijn to the LC type.

fromDB :: Term n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Term n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - (toInt i) -1))
    from n (DLam b) = Lam n (from (succ n) b)
    from n (DApp f a) = App (from n f) (from n a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

instance Show (Term n) where
  show = renderStyle style . ppLC 0

ppLC :: Int -> Term n -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text ("\\.") PP.<> ppLC 0 b
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
