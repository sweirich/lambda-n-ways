{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Natural numbers for dependent types
module Util.Nat where

import Control.DeepSeq (NFData (..))
import Data.Kind (Type)
import Data.Some
import Data.Type.Equality

data Nat = Z | S Nat
  deriving (Eq, Show)

data Idx :: Nat -> Type where
  FZ :: Idx ('S n)
  FS :: Idx n -> Idx ('S n)

data SNat n where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-------------------------------------------

type family Plus n m where
  Plus 'Z n = n
  Plus ('S m) n = 'S (Plus m n)

type family Pred (n :: Nat) :: Nat where
  Pred ('S n) = n

toInt :: Idx n -> Int
toInt FZ = 0
toInt (FS n) = 1 + toInt n

sNat2Int :: SNat n -> Int
sNat2Int SZ = 0
sNat2Int (SS n) = 1 + sNat2Int n

fromInt :: Int -> Some SNat
fromInt 0 = Some SZ
fromInt n | n < 0 = error "negative"
fromInt n = case fromInt (n -1) of
  Some m -> Some (SS m)

fromIntToIdx :: Int -> Some Idx
fromIntToIdx 0 = Some FZ
fromIntToIdx n | n < 0 = error "negative"
fromIntToIdx n = case fromIntToIdx (n -1) of
  Some m -> Some (FS m)

-- update the index by a given amount
shift :: SNat m -> Idx n -> Idx (Plus m n)
shift SZ x = x
shift (SS m) x = FS (shift m x)

-- Keep the index the same, just change its type
weakenIdx :: forall n. Idx n -> Idx ('S n)
weakenIdx FZ = FZ
weakenIdx (FS m) = FS (weakenIdx m)

weakenIdxR :: forall m n. Idx n -> Idx (Plus n m)
weakenIdxR FZ = FZ
weakenIdxR (FS m) = FS (weakenIdxR @m m)

-- either n is equal to m or greater than m
compareIdx :: SNat k -> Idx ('S k) -> Maybe (Idx k)
compareIdx SZ FZ = Nothing
compareIdx (SS m) (FS n) = FS <$> compareIdx m n
compareIdx SZ (FS _) = Nothing
compareIdx (SS _) FZ = Just FZ

-- if n2 is greater than n1 increment it. Otherwise just return it.
cmpIdx :: Idx ('S n) -> Idx n -> Idx ('S n)
cmpIdx n1 n2 =
  case (n1, n2) of
    (FS _m, FZ) -> FZ
    (FS m, FS n) -> FS (cmpIdx m n)
    (FZ, FZ) -> FZ
    (FZ, FS _n) -> FS FZ

instance NFData (Idx a) where
  rnf FZ = ()
  rnf (FS s) = rnf s

instance NFData (SNat a) where
  rnf SZ = ()
  rnf (SS s) = rnf s

instance Show (SNat m) where
  show n = show (toi n)
    where
      toi :: SNat n -> Int
      toi SZ = 0
      toi (SS n) = 1 + toi n

instance Eq (Idx n) where
  FZ == FZ = True
  (FS n) == (FS m) = n == m
  _ == _ = False

instance Show (Idx n) where
  show n = show (toInt n)

----------------------------------------------------

sNat2Idx :: SNat n -> Idx ('S n)
sNat2Idx SZ = FZ
sNat2Idx (SS x) = FS (sNat2Idx x)

instance TestEquality SNat where
  testEquality SZ SZ = Just Refl
  testEquality (SS x) (SS y) = case testEquality x y of
    Just Refl -> Just Refl
    Nothing -> Nothing
  testEquality _ _ = Nothing

-- | Maybe this should be part of Util.Nat???
toIdx :: SNat n -> Int -> Idx n
toIdx (SS _n) 0 = FZ
toIdx (SS n) m | m > 0 = FS (toIdx n (m -1))
toIdx SZ _ = error "No indices in Ix Z"
toIdx _ _m = error "Negative index"
