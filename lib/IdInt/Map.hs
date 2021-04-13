{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module IdInt.Map where

import Control.DeepSeq
import Data.Coerce
import Data.Foldable
import qualified Data.IntMap as M
import IdInt
import IdInt.Set

newtype IdIntMap a = IdIntMap (M.IntMap a) deriving (Eq, Show, Functor, Semigroup, Monoid, NFData, Foldable)

null :: forall a. IdIntMap a -> Bool
null = coerce $ M.null @a

insert :: forall a. IdInt -> a -> IdIntMap a -> IdIntMap a
insert = coerce $ M.insert @a

keysSet :: forall a. IdIntMap a -> IdIntSet
keysSet = coerce $ M.keysSet @a

member :: forall a. IdInt -> IdIntMap a -> Bool
member = coerce $ M.member @a

delete :: forall a. IdInt -> IdIntMap a -> IdIntMap a
delete = coerce $ M.delete @a

restrictKeys :: forall a. IdIntMap a -> IdIntSet -> IdIntMap a
restrictKeys = coerce $ M.restrictKeys @a

empty :: forall a. IdIntMap a
empty = coerce $ M.empty @a

singleton :: forall a. IdInt -> a -> IdIntMap a
singleton = coerce $ M.singleton @a

findWithDefault :: forall a. a -> IdInt -> IdIntMap a -> a
findWithDefault = coerce $ M.findWithDefault @a
