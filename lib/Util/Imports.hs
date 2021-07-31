module Util.Imports
  ( module Control.Applicative,
    module Control.Monad,
    module GHC.Generics,
    module Test.QuickCheck,
    module Control.DeepSeq,
    module Data.Proxy,
    IntMap,
    IntSet,
    Map,
    Seq,
    Set,

    -- * Data.Bifunctor
    second,

    -- * Data.Maybe
    fromJust,fromMaybe,

    -- * "Data.Tuple" reexports
    curry,
    fst,
    snd,
    swap,
    uncurry,

    -- * Data.Coerce
    coerce,

    -- * Data.Kind
    Type,

    -- * Text.ParserCombinators.ReadP
    ReadP,
    Doc,

    -- * Control.Monad.State
    State,
    evalState,
    runState,
    execState,
    MonadState (..),

    -- * Control.Monad.Error
    MonadError (..),
  )
where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Control.Monad.Except (MonadError (..))
import Control.Monad.State
import Data.Bifunctor (second)
import Data.Coerce (coerce)
import Data.IntMap.Strict (IntMap)
import Data.IntSet (IntSet)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Maybe (fromJust, fromMaybe)
import Data.Proxy
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Tuple (curry, fst, snd, swap, uncurry)
import GHC.Generics
import Test.QuickCheck
import Text.ParserCombinators.ReadP (ReadP)
import Text.PrettyPrint.HughesPJ (Doc)
