{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

-- Natural numbers for dependent types
module Util.Nat where

import Control.DeepSeq
import Data.Kind (Type)

data Nat = Z | S Nat
  deriving (Eq, Show)

data Idx :: Nat -> Type where
  FZ :: Idx (S n)
  FS :: Idx n -> Idx (S n)

data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-------------------------------------------

type family Plus n m where
  Plus Z n = n
  Plus (S m) n = S (Plus m n)

type family Pred (n :: Nat) :: Nat where
  Pred (S n) = n

toInt :: Idx n -> Int
toInt FZ = 0
toInt (FS n) = 1 + toInt n

shift :: SNat m -> Idx n -> Idx (Plus m n)
shift SZ x = x
shift (SS m) x = FS (shift m x)

instance NFData (Idx a) where
  rnf FZ = ()
  rnf (FS s) = rnf s

instance NFData (SNat a) where
  rnf SZ = ()
  rnf (SS s) = rnf s

instance Show (SNat m) where
  show SZ = "SZ"
  show (SS n) = "(SS " ++ show n ++ ")"

instance Eq (Idx n) where
  FZ == FZ = True
  (FS n) == (FS m) = n == m
  _ == _ = False

instance Show (Idx n) where
  show FZ = "FZ"
  show (FS n) = "(FS " ++ show n ++ ")"