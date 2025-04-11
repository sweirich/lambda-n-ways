-- Common infrastructure for (strict) implementations with DeBruijn indices
-- Datatype definition, equality, NFData instance, conversion to/from named representation
module Util.Syntax.DeBruijn where

import Control.DeepSeq
import Data.List (elemIndex)
import Text.PrettyPrint.HughesPJ as PP
import Util.IdInt
import Util.Impl
import Util.Imports
import Util.Syntax.Lambda


data DB
  = DVar {-# UNPACK #-} !Int
  | DLam !DB
  | DApp !DB !DB
  | DBool {-# UNPACK #-} !Bool 
  | DIf !DB !DB !DB
  deriving (Eq)

instance NFData DB where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DBool b) = rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c

toDB :: LC IdInt -> DB
toDB = to []
  where
    to vs (Var v@(IdInt i)) = maybe (DVar i) DVar (elemIndex v vs)
    to vs (Lam x b) = DLam (to (x : vs) b)
    to vs (App f a) = DApp (to vs f) (to vs a)
    to vs (Bool b)  = DBool b
    to vs (If a b c) = DIf (to vs a) (to vs b) (to vs c)
fromDB :: DB -> LC IdInt
fromDB = from firstBoundId
  where
    from (IdInt n) (DVar i)
      | i < 0 = Var (IdInt i)
      | i >= n = Var (IdInt i)
      | otherwise = Var (IdInt (n - i -1))
    from n (DLam b) = Lam n (from (succ n) b)
    from n (DApp f a) = App (from n f) (from n a)
    from n (DBool b) = Bool b
    from n (DIf a b c) = If (from n a) (from n b)(from n c)
instance Show DB where
  show = renderStyle style . ppLC 0

ppLC :: Int -> DB -> Doc
ppLC _ (DVar v) = text $ "x" ++ show v
ppLC p (DLam b) = pparens (p > 0) $ text "\\." PP.<> ppLC 0 b
ppLC p (DApp f a) = pparens (p > 1) $ ppLC 1 f <+> ppLC 2 a
ppLC p (DBool b) = text $ show b
ppLC p (DIf a b c) = text "if" PP.<+> ppLC 0 a PP.<+>
                     text "then" PP.<+> ppLC 0 b PP.<+>
                     text "else" PP.<+> ppLC 0 c
pparens :: Bool -> Doc -> Doc
pparens True d = parens d
pparens False d = d