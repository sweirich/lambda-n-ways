-- Common infrastructure for (lazy) implementations with well-scoped
-- DeBruijn indices
-- Datatype definition, equality, NFData instance, conversion to/from named representation
module Util.Syntax.Lazy.ScopedDeBruijn where

import Control.DeepSeq
import Data.List (elemIndex)
import Text.PrettyPrint.HughesPJ as PP
import Util.IdInt
import Util.Impl
import Util.Imports hiding (from, to)
import Util.Syntax.Lambda
import Util.Nat

data Term :: Nat -> Type where
  DVar :: (Idx g) -> Term g
  DLam :: (Term ('S g)) -> Term g
  DApp :: (Term g) -> (Term g) -> Term g
  DBool :: Bool -> (Term g)
  DIf :: (Term g)-> (Term g) -> (Term g) -> Term g

instance NFData (Term a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c

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
    to vs (Bool b)  = DBool b
    to vs (If a b c) = DIf (to vs a) (to vs b) (to vs c)

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
    from n (DBool b) = Bool b
    from n (DIf a b c) = If (from n a) (from n b)(from n c)
mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

instance Show (Term n) where
  show = renderStyle style . ppLC 0

ppLC :: Int -> Term n -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text ("\\.") PP.<> ppLC 0 b
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a
ppLC p (DBool b) = text $ show b
ppLC p (DIf a b c) = text "if" PP.<+> ppLC 0 a PP.<+>
                     text "then" PP.<+> ppLC 0 b PP.<+>
                     text "else" PP.<+> ppLC 0 c

pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d
