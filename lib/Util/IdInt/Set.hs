{-# OPTIONS -fexpose-all-unfoldings #-}

-- | A Finite set of IdInt, based on Data.IntSet
module Util.IdInt.Set
  ( IdIntSet (..),
    empty,
    singleton,
    union,
    (\\),
    toList,
    fromList,
    Util.IdInt.Set.null,
    findMax,
    delete,
    member,
    notMember,
    isSubsetOf,
    insert,
    newIdInt,
    lookupMax,
    varSetMax,
  )
where

import Control.DeepSeq
import Data.Coerce
import qualified Data.IntSet as IntSet
import Util.IdInt

newtype IdIntSet = IdIntSet IntSet.IntSet
  deriving (Eq, Ord, Show, Semigroup, Monoid, NFData)

empty :: IdIntSet
empty = coerce IntSet.empty

singleton :: IdInt -> IdIntSet
singleton = coerce IntSet.singleton

union :: IdIntSet -> IdIntSet -> IdIntSet
union = coerce IntSet.union

(\\) :: IdIntSet -> IdIntSet -> IdIntSet
(\\) = coerce (IntSet.\\)

toList :: IdIntSet -> [IdInt]
toList = coerce IntSet.toList

fromList :: [IdInt] -> IdIntSet
fromList = coerce IntSet.fromList

null :: IdIntSet -> Bool
null = coerce IntSet.null

findMax :: IdIntSet -> IdInt
findMax = coerce IntSet.findMax

delete :: IdInt -> IdIntSet -> IdIntSet
delete = coerce IntSet.delete

notMember :: IdInt -> IdIntSet -> Bool
notMember = coerce IntSet.notMember

member :: IdInt -> IdIntSet -> Bool
member = coerce IntSet.member

isSubsetOf :: IdIntSet -> IdIntSet -> Bool
isSubsetOf = coerce IntSet.isSubsetOf

insert :: IdInt -> IdIntSet -> IdIntSet
insert = coerce IntSet.insert

newIdInt :: IdIntSet -> IdInt
newIdInt (IdIntSet s)
  | IntSet.null s = firstBoundId
  | otherwise = succ (coerce (IntSet.findMax s))

lookupMax :: IdIntSet -> Maybe IdInt
lookupMax s = if coerce IntSet.null s then Nothing else Just (coerce IntSet.findMax s)

varSetMax :: IdIntSet -> IdInt
varSetMax s = maybe (toEnum 0) succ (lookupMax s)
