{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP           #-}
{-# LANGUAGE PatternGuards #-}
----------------------------------------------------------------------
-- |
-- Module      :  Perm
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Portability :  portable
--
-- A slow, but hopefully correct implementation of permutations.
--
----------------------------------------------------------------------

module Perm (
    Perm(..), single, compose, apply, isid, join, empty, restrict, mkPerm,
    Swap(..)
  ) where

import Data.Monoid
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow ((&&&))
import Control.Monad ((>=>))
import Data.Semigroup (Semigroup)
import qualified Data.Semigroup as Semigroup

import Test.QuickCheck

-- | A /permutation/ is a bijective function from names to names
--   which is the identity on all but a finite set of names.  They
--   form the basis for nominal approaches to binding, but can
--   also be useful in general.
newtype Perm a = Perm (Map a a)

permValid :: Ord a => Perm a -> Bool
permValid (Perm p) = all (\(_,v) -> M.member v p) (M.assocs p)
  -- a Map sends every key uniquely to a value by construction.  So if
  -- every value is also a key, the sizes of the domain and range must
  -- be equal and hence the mapping is a bijection.

instance Ord a => Eq (Perm a) where
  (Perm p1) == (Perm p2) =
    all (\x -> M.findWithDefault x x p1 == M.findWithDefault x x p2) (M.keys p1) &&
    all (\x -> M.findWithDefault x x p1 == M.findWithDefault x x p2) (M.keys p2)

instance Show a => Show (Perm a) where
  show (Perm p) = show p

-- | Apply a permutation to an element of the domain.
apply :: Ord a => Perm a -> a -> a
apply (Perm p) x = M.findWithDefault x x p

-- | Create a permutation which swaps two elements.
single :: Ord a => a -> a -> Perm a
single x y = if x == y then Perm M.empty else
    Perm (M.insert x y (M.insert y x M.empty))

-- | The empty (identity) permutation.
empty :: Perm a
empty = Perm M.empty

-- | Compose two permutations.  The right-hand permutation will be
--   applied first.
compose :: Ord a => Perm a -> Perm a -> Perm a
compose (Perm b) (Perm a) =
  Perm (M.fromList ([ (x,M.findWithDefault y y b) | (x,y) <- M.toList a]
         ++ [ (x, M.findWithDefault x x b) | x <- M.keys b, M.notMember x a]))

-- | Permutations form a monoid under composition.
instance Ord a => Semigroup (Perm a) where
  (<>) = compose

-- | Permutations form a monoid under composition.
instance Ord a => Monoid (Perm a) where
  mempty  = empty
#if !MIN_VERSION_base(4,11,0)  
  mappend = (Semigroup.<>)
#endif

-- | Is this the identity permutation?
isid :: Ord a => Perm a -> Bool
isid (Perm p) =
     M.foldrWithKey (\ a b r -> r && a == b) True p

-- | /Join/ two permutations by taking the union of their relation
--   graphs. Fail if they are inconsistent, i.e. map the same element
--   to two different elements.
join :: Ord a => Perm a -> Perm a -> Maybe (Perm a)
join (Perm p1) (Perm p2) =
     let overlap = M.intersectionWith (==) p1 p2 in
#if MIN_VERSION_containers(0,5,0)     
     if M.foldr (&&) True overlap then
#else
     if M.fold (&&) True overlap then
#endif
       Just (Perm (M.union p1 p2))
       else Nothing

-- | The /support/ of a permutation is the set of elements which are
--   not fixed.
supportPerm :: Ord a => Perm a -> S.Set a
supportPerm (Perm p) = S.fromList [ x | x <- M.keys p, M.findWithDefault x x p /= x]

-- | Restrict a permutation to a certain domain.
restrict :: Ord a => Perm a -> [a] -> Perm a
restrict (Perm p) l = Perm (foldl' (flip M.delete) p l)

-- | A partial permutation consists of two maps, one in each direction
--   (inputs -> outputs and outputs -> inputs).
data PartialPerm a = PP (M.Map a a) (M.Map a a)
  deriving Show

emptyPP :: PartialPerm a
emptyPP = PP M.empty M.empty

extendPP :: Ord a => a -> a -> PartialPerm a -> Maybe (PartialPerm a)
extendPP x y pp@(PP mfwd mrev)
  | Just y' <- M.lookup x mfwd = if y == y' then Just pp
                                            else Nothing
  | Just x' <- M.lookup y mrev = if x == x' then Just pp
                                            else Nothing
  | otherwise = Just $ PP (M.insert x y mfwd) (M.insert y x mrev)

-- | Convert a partial permutation into a full permutation by closing
--   off any remaining open chains into a cycles.
ppToPerm :: Ord a => PartialPerm a -> Perm a
ppToPerm (PP mfwd mrev) = Perm $ foldr (uncurry M.insert . (findEnd &&& id)) mfwd chainStarts
{-
foldr (uncurry M.insert) mfwd
                                       (map (findEnd &&& id) chainStarts)
-}
        -- beginnings of open chains are elements which map to
        -- something in the forward direction but have no ancestor.
  where chainStarts = S.toList (M.keysSet mfwd `S.difference` M.keysSet mrev)
        findEnd x = maybe x findEnd (M.lookup x mfwd)
                   

-- | @mkPerm l1 l2@ creates a permutation that sends @l1@ to @l2@.
--   Fail if there is no such permutation, either because the lists
--   have different lengths or because they are inconsistent (which
--   can only happen if @l1@ or @l2@ have repeated elements).
mkPerm :: Ord a => [a] -> [a] -> Maybe (Perm a)
mkPerm xs ys
  | length xs /= length ys = Nothing
  | otherwise =
    fmap ppToPerm . ($emptyPP) . foldr (>=>) return $ zipWith extendPP xs ys


-- | Class of types that allow swapping
class Swap a b where
  swap    :: Ord a => Perm a -> b -> b
  swap _p = id
  support :: Ord a => b -> S.Set a
  support = const S.empty
  
instance {-# OVERLAPPING #-} Swap a a where
  swap    = apply
  support = S.singleton
instance {-# OVERLAPPING #-} Swap a (Perm a) where
  swap p1 p2 = compose p1 p2
  support = supportPerm

instance Swap a (Perm b) 
instance Swap a () 
instance Swap a Char 
instance Swap a Bool 
instance (Swap c a, Swap c b) => Swap c (Either a b) where
  swap p (Left x) = Left (swap p x)
  swap p (Right x) = Right (swap p x)
  support (Left x) = support x
  support (Right x) = support x
instance (Swap c a, Swap c b) => Swap c (a,b) where
  swap p (x,y) = (swap p x, swap p y)
  support (x,y) = support x `S.union` support y
instance (Swap c a) => Swap c [a] where
  swap p = fmap (swap p)
  support xs = foldr (\x s -> support x `S.union` s) S.empty xs
instance (Swap c a, Swap c b) => Swap c (a -> b) where
  swap p f = swap p . f . swap p
  support = error "fn support undefined"

------------------------------------------------------------------------------
-- Testing code for permutations

instance (Ord a, Arbitrary a) => Arbitrary (Perm a) where
  arbitrary = do xs <- listOf arbitrary
                 return $ go xs empty
    where
      go []       p = p
      go [x]   p = p
      go (x:y:xs) p 
       | x `elem` support p || y `elem` support p = go xs p
       | otherwise  = go xs (single x y <> p)

  shrink (Perm m) = case M.lookupMax m of
    Nothing     -> []
    Just (x, y) -> [Perm (M.delete x (M.delete y m))]

prop_valid :: Perm Int -> Bool
prop_valid = permValid

prop_shrink :: Perm Int -> Bool
prop_shrink p = all permValid (shrink p)

prop_empty :: Int -> Bool
prop_empty x = swap (empty :: Perm Int) x == x

prop_compose :: Perm Int -> Perm Int -> Int -> Bool
prop_compose p1 p2 x = swap p1 (swap p2 x) == swap (p1 <> p2) x

prop_idL :: Perm Int -> Int -> Bool
prop_idL p x = swap (empty <> p) x == swap p x

prop_idR :: Perm Int -> Int -> Bool
prop_idR p x = swap (p <> empty) x == swap p x

prop_assoc :: Perm Int -> Perm Int -> Perm Int -> Int -> Bool
prop_assoc p1 p2 p3 x =
  swap (p1 <> (p2 <> p3)) x == swap ((p1 <> p2) <> p3) x
