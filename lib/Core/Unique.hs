

{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998


@Uniques@ are used to distinguish entities in the compiler (@Ids@,
@Classes@, etc.) from each other.  Thus, @Uniques@ are the basic
comparison key in the compiler.

If there is any single operation that needs to be fast, it is @Unique@

comparison.  Unsurprisingly, there is quite a bit of huff-and-puff
directed to that end.

Some of the other hair in this code is to be able to use a
``splittable @UniqueSupply@'' if requested/possible (not standard
Haskell).
-}

module Core.Unique (
        -- * Main data types
        Unique(..), Uniquable(..),

        -- ** Constructors, destructors and operations on 'Unique's
        hasKey,
        mkUniqueGrimily,
        getKey,
        eqUnique, ltUnique,
        incrUnique, stepUnique,
        nonDetCmpUnique,

        -- ** Local uniques
        -- | These are exposed exclusively for use by 'VarEnv.uniqAway', which
        -- has rather peculiar needs. See Note [Local uniques].
        mkLocalUnique, minLocalUnique, maxLocalUnique


    ) where

{-

import GHC.Prelude

import GHC.Types.Basic
import GHC.Data.FastString
import GHC.Utils.Outputable
import GHC.Utils.Misc

-- just for implementing a fast [0,61) -> Char function
import GHC.Exts (indexCharOffAddr#, Char(..), Int(..))
-}

-- | Avoid orphan instance

import Util.IdInt

instance Uniquable IdInt where
    getUnique (IdInt i) = getUnique i

{-
************************************************************************
*                                                                      *
\subsection[Unique-type]{@Unique@ type and operations}
*                                                                      *
************************************************************************

The @Chars@ are ``tag letters'' that identify the @UniqueSupply@.
Fast comparison is everything on @Uniques@:
-}

-- | Unique identifier.
--
-- The type of unique identifiers that are used in many places in GHC
-- for fast ordering and equality tests. You should generate these with
-- the functions from the 'UniqSupply' module
--
-- These are sometimes also referred to as \"keys\" in comments in GHC.
newtype Unique = MkUnique Int


mkUniqueGrimily :: Int -> Unique                -- A trap-door for UniqSupply
getKey          :: Unique -> Int                -- for Var

mkUniqueGrimily = MkUnique

{-# INLINE getKey #-}
getKey (MkUnique x) = x


-- Note [Unique Determinism and code generation]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- The goal of the deterministic builds (wiki/deterministic-builds, #4012)
-- is to get ABI compatible binaries given the same inputs and environment.
-- The motivation behind that is that if the ABI doesn't change the
-- binaries can be safely reused.
-- Note that this is weaker than bit-for-bit identical binaries and getting
-- bit-for-bit identical binaries is not a goal for now.
-- This means that we don't care about nondeterminism that happens after
-- the interface files are created, in particular we don't care about
-- register allocation and code generation.
-- To track progress on bit-for-bit determinism see #12262.

eqUnique :: Unique -> Unique -> Bool
eqUnique (MkUnique u1) (MkUnique u2) = u1 == u2

ltUnique :: Unique -> Unique -> Bool
ltUnique (MkUnique u1) (MkUnique u2) = u1 < u2

-- Provided here to make it explicit at the call-site that it can
-- introduce non-determinism.
-- See Note [Unique Determinism]
-- See Note [No Ord for Unique]
nonDetCmpUnique :: Unique -> Unique -> Ordering
nonDetCmpUnique (MkUnique u1) (MkUnique u2)
  = if u1 == u2 then EQ else if u1 < u2 then LT else GT

{-
Note [No Ord for Unique]
~~~~~~~~~~~~~~~~~~~~~~~~~~
As explained in Note [Unique Determinism] the relative order of Uniques
is nondeterministic. To prevent from accidental use the Ord Unique
instance has been removed.
This makes it easier to maintain deterministic builds, but comes with some
drawbacks.
The biggest drawback is that Maps keyed by Uniques can't directly be used.
The alternatives are:

  1) Use UniqFM or UniqDFM, see Note [Deterministic UniqFM] to decide which
  2) Create a newtype wrapper based on Unique ordering where nondeterminism
     is controlled. See Module.ModuleEnv
  3) Change the algorithm to use nonDetCmpUnique and document why it's still
     deterministic
  4) Use TrieMap as done in GHC.Cmm.CommonBlockElim.groupByLabel
-}

instance Eq Unique where
    a == b = eqUnique a b
    a /= b = not (eqUnique a b)

instance Uniquable Unique where
    getUnique u = u

-- We do sometimes make strings with @Uniques@ in them:

showUnique :: Unique -> String
showUnique (MkUnique i)
  = show i

instance Show Unique where
    show uniq = showUnique uniq

incrUnique :: Unique -> Unique
stepUnique   :: Unique -> Int -> Unique
incrUnique (MkUnique i) = MkUnique (i + 1)
stepUnique (MkUnique i) n = MkUnique (i + n)

mkLocalUnique :: Int -> Unique
mkLocalUnique = MkUnique

minLocalUnique :: Unique
minLocalUnique = MkUnique 0

maxLocalUnique :: Unique
maxLocalUnique = MkUnique maxBound


{-
************************************************************************
*                                                                      *
\subsection[Uniquable-class]{The @Uniquable@ class}
*                                                                      *
************************************************************************
-}

-- | Class of things that we can obtain a 'Unique' from
class Uniquable a where
    getUnique :: a -> Unique

hasKey          :: Uniquable a => a -> Unique -> Bool
x `hasKey` k    = getUnique x == k



instance Uniquable Int where
 getUnique i = mkUniqueGrimily i

