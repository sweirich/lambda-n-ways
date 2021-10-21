{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

-- Efficient normalization by evaluation
-- Mathieu Boespflug
-- https://hal.inria.fr/inria-00434283/document

-- Operational aspects of untyped Normalisation by Evaluation
-- KLAUS AEHLIG† and FELIX JOACHIMSKI
-- https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/operational-aspects-of-untyped-normalisation-by-evaluation/18A966EEA5E5760D3DBCCBECF4A9EC0D
-- MSCS 2004

module NBE.Boesflug (impl) where

import qualified Data.Map as M
import Data.Maybe (fromJust, fromMaybe)
import Util.IdInt
import Util.Impl
import Util.Syntax.DeBruijn
import qualified Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Aelig",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nf,
      impl_nfi = error "undefiend",
      impl_aeq = (==)
    }

data Term
  = Const IdInt
  | Abs (Term -> Term)
  | App Term Term

data NF
  = N Neutral
  | NAbs (NF -> NF)

data Neutral
  = NConst IdInt
  | NApp Neutral NF

inj :: NF -> Term
inj (N (NConst x)) = Const x
inj (N (NApp x y)) = App (inj (N x)) (inj y)
inj (NAbs f) = Abs (\x -> inj (f (normalize x)))

normalize :: Term -> NF
normalize (Const x) = N (NConst x)
normalize (Abs f) =
  NAbs (\x -> normalize (f (inj x)))
normalize (App t1 t2) =
  case normalize t1 of
    NAbs f -> f (normalize t2)
    N t -> N (NApp t (normalize t2))

app :: Term -> Term -> Term
app (Abs t1) t2 = t1 t2
app t1 t2 = App t1 t2

nf :: Term -> Term
nf = inj . normalize

fromLC :: LC.LC IdInt -> Term
fromLC = from M.empty
  where
    from m (LC.Var v) = fromMaybe (Const v) (M.lookup v m)
    from m (LC.Lam v e) = Abs $ \x -> from (M.insert v x m) e
    from m (LC.App f a) = App (from m f) (from m a)

toLC :: Term -> LC.LC IdInt
toLC = to firstBoundId
  where
    to _ (Const v) = LC.Var v
    to n (Abs b) = LC.Lam n (to (succ n) (b (HVar n)))
    to n (App f a) = LC.App (to n f) (to n a)
