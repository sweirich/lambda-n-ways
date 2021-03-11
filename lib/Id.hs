-- String based identifiers
module Id where

import Data.Char (isAlphaNum)
import Imports

newtype Id = Id String
  deriving (Eq, Ord, NFData, Generic)

-- Identifiers print and parse without any adornment.
instance Show Id where
  show (Id i) = i

instance Read Id where
  readsPrec _ s =
    case span isAlphaNum s of
      ("", _) -> []
      (i, s') -> [(Id i, s')]

instance Arbitrary Id where
  arbitrary = Id <$> genSafeString

genSafeChar :: Gen Char
genSafeChar = elements ['a' .. 'z']

genSafeString :: Gen String
genSafeString = listOf1 genSafeChar

-- Round trip property for parsing / pp
--prop_roundTrip :: LC Id -> Bool
--prop_roundTrip x = read (show x) == x