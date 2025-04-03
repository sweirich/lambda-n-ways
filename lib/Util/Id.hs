-- | String based identifiers
module Util.Id where

import Data.Char (isAlphaNum)
import Util.Imports

newtype Id = Id String
  deriving (Eq, Ord, NFData, Generic)

reserved = ["true", "false","if","then","else","let"]

-- Identifiers print and parse without any adornment.
instance Show Id where
  show (Id i) = i

instance Read Id where
  readsPrec _ s | s `notElem` reserved =
    case span isAlphaNum s of
      ("", _) -> []
      (i, s') -> [(Id i, s')]
                | otherwise = []

instance Arbitrary Id where
  arbitrary = Id <$> genSafeString

genSafeChar :: Gen Char
genSafeChar = elements ['a' .. 'z']

genSafeString :: Gen String
genSafeString = listOf1 genSafeChar

-- Round trip property for parsing / pp
--prop_roundTrip :: LC Id -> Bool
--prop_roundTrip x = read (show x) == x