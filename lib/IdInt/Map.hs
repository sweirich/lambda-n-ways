{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module IdInt.Map where

import Control.DeepSeq (NFData)
import Data.Coerce (coerce)
import qualified Data.IntMap as M
import IdInt (IdInt (..))
import IdInt.Set (IdIntSet (..))

newtype IdIntMap a = IdIntMap (M.IntMap a)
  deriving (Eq, Show, Functor, Semigroup, Monoid, NFData, Foldable, Traversable)

null :: forall a. IdIntMap a -> Bool
null = coerce $ M.null @a

elems :: forall a. IdIntMap a -> [a]
elems = coerce $ M.elems @a

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
