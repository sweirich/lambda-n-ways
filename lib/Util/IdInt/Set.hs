-- | A Finite set of IdInt, based on Data.IntSet
module Util.IdInt.Set
  ( IdIntSet (..),
    empty,
    singleton,
    union,
    (\\),
    toList,
    Util.IdInt.Set.null,
    findMax,
    delete,
    member,
    notMember,
    isSubsetOf,
    insert,
    newIdInt,
  )
where

import Control.DeepSeq
import Data.Coerce
import qualified Data.IntSet as IntSet
import Util.IdInt
import Util.Lambda hiding (freeVars)

newtype IdIntSet = IdIntSet IntSet.IntSet deriving (Eq, Ord, Show, Semigroup, Monoid, NFData)

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