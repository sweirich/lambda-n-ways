{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module IdInt.Set(IdIntSet(..)
      , empty
      , singleton
      , union
      , (\\)
      , toList
      , IdInt.Set.null
      , findMax
      , delete
      , member
      , notMember
      , isSubsetOf

      , freeVars
      ) where

import IdInt
import qualified Data.IntSet as IntSet
import Data.Coerce 
import Lambda hiding (freeVars)
import Control.DeepSeq

-- A set of IdInts, based on Data.IntSet

newtype IdIntSet = IdIntSet IntSet.IntSet deriving (Eq, Show, Semigroup, Monoid, NFData)

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

member  :: IdInt -> IdIntSet -> Bool
member = coerce IntSet.member

isSubsetOf :: IdIntSet -> IdIntSet -> Bool
isSubsetOf = coerce IntSet.isSubsetOf


freeVars :: LC IdInt -> IdIntSet
freeVars (Var v)   = singleton v
freeVars (Lam v e) = freeVars e \\ singleton v
freeVars (App f a) = freeVars f `union` freeVars a
