{-# LANGUAGE TemplateHaskell #-}

module Abstract.Unbound where

import Abstract.Class (Arbitrary (..), IdInt (..), LC (..), NFData (..))
import qualified Abstract.Class as A hiding (R, Rep, from, to, (:*:))
import Abstract.Simple
import Unbound.LocallyNameless as U hiding (from, to)

newtype U = U (Name (LC U))
  deriving (Eq, Ord, Show, Read, Arbitrary, NFData)

instance Alpha U

-- Annoyingly, need a new type here b/c Unbound doesn't expose that U.Bind
-- is a data constructor
--newtype UBind a b = UBind (U.Bind a b)
--  deriving (Show, Read, Arbitrary, NFData, U.Alpha)

instance U.Subst (LC U) U

instance U.Subst (LC U) (LC U) where
  isvar (Var (U x)) = Just (U.SubstName x)
  isvar _ = Nothing

newtype Scope a = Scope a deriving (Eq, NFData)

n2i :: U -> IdInt
n2i (U n) = IdInt (fromInteger (name2Integer n))

i2n :: IdInt -> U
i2n (IdInt x) = U (s2n (show x))

toDB :: LC IdInt -> LC U
toDB = to
  where
    to :: LC IdInt -> LC U
    to (Var v) = Var (i2n v)
    to (Lam (x, b)) = Lam (U.bind (i2n x) (to b))
    to (App f a) = App (to f) (to a)

fromDB :: LC U -> LC IdInt
fromDB = runFreshM . from

from :: LC U -> U.FreshM (LC IdInt)
from (Var n) = return $ Var (n2i n)
from (Lam b) = do
  (x, a) <- U.unbind b
  a' <- from a
  return $ Lam (n2i x, a')
from (App f a) = App <$> from f <*> from a

instance U.Alpha (LC U)

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

$(derive [''LC, ''U])