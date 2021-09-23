module Util.Vec where

import Util.Imports hiding (S)
import Util.Nat
import Prelude hiding (length)

data Vec (n :: Nat) a where
  VNil :: Vec 'Z a
  VCons :: a -> Vec n a -> Vec ('S n) a

deriving instance Functor (Vec n)

deriving instance Show a => Show (Vec n a)

instance NFData a => NFData (Vec n a) where
  rnf VNil = ()
  rnf (VCons a b) = rnf a `seq` rnf b

length :: Vec n a -> SNat n
length VNil = SZ
length (VCons _ vs) = SS (length vs)

-- | access via singleton
nth :: SNat n -> Vec ('S n) a -> a
nth SZ (VCons a _) = a
nth (SS m) (VCons _ ss) = nth m ss

-- | access via index
inth :: Idx n -> Vec n a -> a
inth FZ (VCons a _) = a
inth (FS m) (VCons _ ss) = inth m ss

append :: Vec m a -> Vec n a -> Vec (Plus m n) a
append VNil v = v
append (VCons u vm) vn = VCons u (append vm vn)