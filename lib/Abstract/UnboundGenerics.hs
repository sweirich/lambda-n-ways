{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Abstract.UnboundGenerics where

import Abstract.Class (Arbitrary (..), IdInt (..), LC (..), NFData (..))
import qualified Abstract.Class as A hiding (R, Rep, from, to, (:*:))
import Abstract.Simple
import GHC.Generics (Generic)
import qualified Text.Read as R
import Unbound.Generics.LocallyNameless as U

newtype U = U (Name (LC U))
  deriving (Eq, Ord, Show, NFData, Generic)

instance Read U where
  readsPrec d s = map (\(x, y) -> (U (s2n x), y)) parses
    where
      parses = R.lex s

instance Arbitrary U where
  arbitrary = U <$> (s2n <$> arbitrary)

instance U.Alpha U

instance U.Alpha (LC U)

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.
instance U.Subst (LC U) U

instance U.Subst (LC U) (LC U) where
  isvar (Var (U x)) = Just (U.SubstName x)
  isvar _ = Nothing

instance A.BindingImpl U where
  type Bnd U = U.Bind U (LC U)
  type Subst U = (,) U
  type BindM U = U.FreshM
  runBindM = U.runFreshM

  aeq x y = return $ U.aeq x y
  bind v a = return $ U.bind v a
  unbind b = U.unbind b
  toLC = from
  fromLC a = return $ toDB a

  singleton _v a = (i2n (IdInt 0), a)
  subst (U n, a) v = return $ U.subst n a v

-- Convert back from deBruijn to the LC type.

n2i :: U -> IdInt
n2i (U n) = IdInt (fromInteger (name2Integer n))

i2n :: IdInt -> U
i2n (IdInt x) = U (s2n (show x))

from :: LC U -> U.FreshM (LC IdInt)
from (Var n) = return $ Var (n2i n)
from (Lam b) = do
  (x, a) <- unbind b
  a' <- from a
  return $ Lam (n2i x, a')
from (App f a) = App <$> from f <*> from a

toDB :: LC IdInt -> LC U
toDB = to
  where
    to :: LC IdInt -> LC U
    to (Var v) = Var (i2n v)
    to (Lam (x, b)) = Lam (U.bind (i2n x) (to b))
    to (App f a) = App (to f) (to a)