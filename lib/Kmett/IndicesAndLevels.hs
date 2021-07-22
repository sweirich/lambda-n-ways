{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- {-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NPlusKPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- {-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- | Code by Edward Kmett
-- https://gist.github.com/ekmett/2082a22e16a4f9b16e301784fb4de0d5
-- Original version requires GHC 8.10.1 or later
module Kmett.IndicesAndLevels where

import Control.Category
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Data.Bits
import Data.Coerce
import Data.Functor
-- see github.com/ekmett/haskell types, mostly used because I can't be bothered to strip it out, not important

--import Data.Type.Unsafe

import Data.Hashable
import Data.IORef
import Data.Kind
import Data.Maybe
import Data.Proxy
import Data.Type.Equality hiding (apply)
import GHC.Exts (Proxy# (..))
import GHC.TypeNats
import Kmett.Type hiding (SCons, SNil)
import Numeric.Natural
import System.IO.Unsafe
import Text.Show.Deriving
import Unsafe.Coerce
import Prelude hiding (id, (.))

-- efficient singleton representation for Nat
newtype Ix (i :: Int) = Ix Int
  deriving newtype (Show)

--------------------------------------------------------------------------------

-- * De Bruijn Indices

--------------------------------------------------------------------------------

-- Analogue to Fin type
data Ix' (i :: Int) where
  IZ' :: Ix' (S n)
  IS' :: Ix n -> Ix' (S n)

ix' :: Ix i -> Ix' i
ix' (Ix 0) = unsafeCoerce IZ'
ix' (Ix n) = unsafeCoerce (IS' (Ix (n -1)))

pattern IZ :: () => n ~ (S n') => Ix n
pattern IZ <-
  (ix' -> IZ')
  where
    IZ = Ix 0

pattern IS :: () => n ~ S n' => Ix n' -> Ix n
pattern IS n <-
  (ix' -> IS' n)
  where
    IS (Ix n) = Ix (n + 1)

--------------------------------------------------------------------------------

-- * De Bruijn Levels

--------------------------------------------------------------------------------

newtype Lvl = Lvl Int
  deriving newtype (Eq, Ord, Show, Read, Num, Enum, Real, Integral)

lvlIx :: forall i. Sing i => Lvl -> Ix i
lvlIx (Lvl l) = Ix (reflect @_ @i - l - 1)

ixLvl :: forall i. Sing i => Ix i -> Lvl
ixLvl (Ix l) = Lvl (reflect @_ @i - l - 1)

--------------------------------------------------------------------------------

-- * Environments (Vectors)

--------------------------------------------------------------------------------

type role Tree nominal nominal representational

data Tree (i :: Int) (j :: Int) (a :: Type) where
  TTip :: ~a -> Tree (S j) j a
  TBin :: ~a -> Tree j k a -> Tree k l a -> Tree (S j) l a

instance Functor (Tree i j) where
  fmap f (TTip a) = TTip (f a)
  fmap f (TBin a l r) = TBin (f a) (fmap f l) (fmap f r)

instance Foldable (Tree i j) where
  foldMap f (TTip a) = f a
  foldMap f (TBin a l r) = f a <> foldMap f l <> foldMap f r

instance Traversable (Tree i j) where
  traverse f (TTip a) = TTip <$> f a
  traverse f (TBin a l r) = TBin <$> f a <*> traverse f l <*> traverse f r

-- TODO: functor, foldable, traversable, applicative, monad

type role Vec nominal representational

data Vec (n :: Int) (a :: Type) where
  TCons :: Int -> Int -> Tree n m a -> Vec m a -> Vec n a
  Nil :: Vec Z a

instance Functor (Vec n) where
  fmap _ Nil = Nil
  fmap f (TCons s n t xs) = TCons s n (fmap f t) (fmap f xs)

instance Foldable (Vec n) where
  foldMap _ Nil = mempty
  foldMap f (TCons s n t xs) = foldMap f t <> foldMap f xs
  null Nil = True
  null _ = False
  length Nil = 0
  length (TCons s _ _ _) = s

-- TODO: functor, foldable, traversable, applicative, monad

type role Vec' nominal representational

data Vec' (n :: Int) (a :: Type) where
  Nil' :: Vec' Z i
  Cons' :: ~a -> Vec n a -> Vec' (S n) a

vcons :: a -> Vec j a -> Vec (S j) a
vcons a (TCons s n l (TCons _ m r xs))
  | n == m = TCons (s + 1) (2 * n + 1) (TBin a l r) xs
vcons a xs = TCons (1 + length xs) 1 (TTip a) xs

upVec :: Vec i a -> Vec' i a
upVec Nil = Nil'
upVec (TCons _ _ (TTip a) xs) = Cons' a xs
upVec (TCons s n (TBin a l r) xs) = Cons' a $ TCons (s -1) n' l $ TCons (s -1 - n') n' r xs
  where
    n' = unsafeShiftR n 1

pattern (:*) :: () => n ~ S m => a -> Vec m a -> Vec n a
pattern v :* e <-
  (upVec -> Cons' v e)
  where
    v :* e = vcons v e

infixr 5 :*

{-# COMPLETE Nil, (:*) #-}

index :: Vec i a -> Ix i -> a
index = go
  where
    go :: Vec i a -> Ix i -> a
    go (TCons _ n t xs) !m@(Ix im)
      | n <= im = go xs (Ix (im - n))
      | otherwise = goTree n t m
    go Nil _ = panic

    goTree :: Int -> Tree j k a -> Ix j -> a
    goTree _ (TTip a) IZ = a
    goTree _ (TTip _) _ = panic
    goTree _ (TBin a _ _) IZ = a
    goTree n (TBin _ l r) m@(Ix im)
      | im <= n' = goTree n' l $ Ix (im - 1)
      | otherwise = goTree n' r $ Ix (im - n' - 1)
      where
        n' = unsafeShiftR n 1

-------------------------------------------------------------------------------

-- * Expressions

-------------------------------------------------------------------------------

type Name = String

-- The index on this datatype definition is the number of free variables in the
-- term. It is a fairly standard typed de Bruijn index representation
data Tm i where
  Var :: Ix i -> Tm i
  App :: Tm i -> Tm i -> Tm i
  Lam :: Name -> Tm (S i) -> Tm i

-------------------------------------------------------------------------------

-- * Semantic Domain

-------------------------------------------------------------------------------

data Val where
  VLam :: Name -> EVal -> Val
  VVar :: Lvl -> Sp -> Val

type EVal = Val -> IO Val

lvlVar :: Sing i => Lvl -> Tm i
lvlVar h = Var (lvlIx h)

topLvl :: forall (i :: Int). SingI i => Lvl
topLvl = Lvl (reflect @Int @i)

topVal :: forall (i :: Int). SingI i => Val
topVal = VVar (topLvl @i) SNil

-- Spine - a right-to-left sequence of applications
data Sp where
  SNil :: Sp
  SApp :: Sp -> ~Val -> Sp -- arg is lazy

{-# COMPLETE SNil, SApp #-}

panic :: a
panic = error "panic"

-------------------------------------------------------------------------------

-- * Utilities

-------------------------------------------------------------------------------

lazily :: IO a -> IO a
lazily = unsafeInterleaveIO

type Vals (i :: Int) = Vec i Val

vskip :: Vals i -> Vals (S i)
vskip vs = VVar (Lvl $ length vs) SNil :* vs

-------------------------------------------------------------------------------

-- * Evaluation (NBE)

-------------------------------------------------------------------------------

lazilyEval :: Vals i -> Tm i -> IO Val
lazilyEval e t = lazily (eval e t)

eval :: Vals i -> Tm i -> IO Val
eval e (Var n) = pure $ index e n
eval e (App f x) = do
  fv <- eval e f
  xv <- lazilyEval e x
  apply fv xv
eval e (Lam n b) = do
  pure $ VLam n \v -> eval (v :* e) b

apply :: Val -> Val -> IO Val
apply (VLam _ f) v = f v
apply (VVar h s) v = pure $ VVar h (SApp s v)
apply _ _ = panic

applySp :: Val -> Sp -> IO Val
applySp h SNil = pure h
applySp h (SApp sp u) = do
  sp' <- applySp h sp
  apply sp' u

quote :: forall n. Sing n => Val -> IO (Tm n)
quote (VLam n b) = do
  Lam n <$> do
    v' <- b (topVal @n)
    quote v'
quote (VVar h s) = quoteSp s (lvlVar h)

quoteSp :: Sing i => Sp -> Tm i -> IO (Tm i)
quoteSp SNil e = pure e
quoteSp (SApp s x) e = App <$> quoteSp s e <*> quote x

nf :: Sing j => Vals i -> Tm i -> IO (Tm j)
nf e t = eval e t >>= quote

-------------------------------------------------------------------------------

-- * Evaluation (NBE, in an arbitrary monad)

data MVal m where
  MVLam :: Name -> (MVal m -> m (MVal m)) -> MVal m
  MVVar :: Lvl -> MSp m -> MVal m

type MVals m (i :: Int) = Vec i (MVal m)

topMVal :: forall (i :: Int) m. SingI i => MVal m
topMVal = MVVar (topLvl @i) MSNil

data MSp m where
  MSNil :: MSp m
  MSApp :: MSp m -> ~(MVal m) -> MSp m -- arg is lazy

evalm :: Monad m => MVals m i -> Tm i -> m (MVal m)
evalm e (Var n) = pure $ index e n
evalm e (App f x) = do
  fv <- evalm e f
  xv <- evalm e x
  applym fv xv
evalm e (Lam n b) = do
  pure $ MVLam n \v -> evalm (v :* e) b

applym :: Monad m => MVal m -> MVal m -> m (MVal m)
applym (MVLam _ f) v = f v
applym (MVVar h s) v = pure $ MVVar h (MSApp s v)
applym _ _ = panic

applySpm :: Monad m => MVal m -> MSp m -> m (MVal m)
applySpm h MSNil = pure h
applySpm h (MSApp sp u) = do
  sp' <- applySpm h sp
  applym sp' u

quotem :: forall n m. (Sing n, Monad m) => (MVal m) -> m (Tm n)
quotem (MVLam n b) = do
  Lam n <$> do
    v' <- b (topMVal @n)
    quotem v'
quotem (MVVar h s) = quoteSpm s (lvlVar h)

quoteSpm :: (Monad m, Sing i) => MSp m -> Tm i -> m (Tm i)
quoteSpm MSNil e = pure e
quoteSpm (MSApp s x) e = App <$> quoteSpm s e <*> quotem x

nfm :: (Monad m, Sing j) => MVals m i -> Tm i -> m (Tm j)
nfm e t = evalm e t >>= quotem

-------------------------------------------------------------------------------

-- * Pure NBE, not in a monad

data PVal where
  PVLam :: Name -> (PVal -> PVal) -> PVal
  PVVar :: Lvl -> PSp -> PVal

type PVals (i :: Int) = Vec i (PVal)

topPVal :: forall (i :: Int) m. SingI i => PVal
topPVal = PVVar (topLvl @i) PSNil

data PSp where
  PSNil :: PSp
  PSApp :: PSp -> ~(PVal) -> PSp -- arg is lazy

evalp :: PVals i -> Tm i -> PVal
evalp e (Var n) = index e n
evalp e (App f x) = do
  let fv = evalp e f
  let xv = evalp e x
  applyp fv xv
evalp e (Lam n b) = do
  PVLam n \v -> evalp (v :* e) b

applyp :: PVal -> PVal -> PVal
applyp (PVLam _ f) v = f v
applyp (PVVar h s) v = PVVar h (PSApp s v)
applyp _ _ = panic

applySpp :: PVal -> PSp -> (PVal)
applySpp h PSNil = h
applySpp h (PSApp sp u) = do
  let sp' = applySpp h sp
  applyp sp' u

quotep :: forall n. (Sing n) => (PVal) -> (Tm n)
quotep (PVLam n b) = do
  Lam n $ do
    let v' = b (topPVal @n)
    quotep v'
quotep (PVVar h s) = quoteSpp s (lvlVar h)

quoteSpp :: (Sing i) => PSp -> Tm i -> Tm i
quoteSpp PSNil e = e
quoteSpp (PSApp s x) e = App (quoteSpp s e) (quotep x)

nfp :: (Sing j) => PVals i -> Tm i -> (Tm j)
nfp e t = quotep (evalp e t)

-------------------------------------------------------------------------------

-- Normal order reduction
-- First argument is an environment (i.e. delayed substitution?)
-- What happens if the term is open?

data NVal i where
  NVLam :: Name -> (Tm i -> NVal i) -> NVal i
  NVVar :: Lvl -> NSp i -> NVal i

type NVals (i :: Int) = Vec i (NVal i)

topNVal :: forall (i :: Int) j. SingI i => NVal j
topNVal = NVVar (topLvl @i) NSNil

data NSp i where
  NSNil :: NSp
  NSApp :: NSp i -> ~(NVal i) -> PSp -- arg is lazy

red :: NVals i -> Tm i -> NVal i
red e (Var n) = index e n
red e (App f x) = do
  let fv = evalp e f
  applyr fv x
red e (Lam n b) = do
  NVLam n \v -> red (v :* e) b

applyr :: NVal -> Tm i -> NVal
applyr (PVLam _ f) v = f v
applyr (PVVar h s) v = NVVar h (PSApp s v)
applyr _ _ = panic

applySpr :: PVal -> PSp -> (PVal)
applySpr h PSNil = h
applySpr h (PSApp sp u) = do
  let sp' = applySpp h sp
  applyp sp' u

quotep :: forall n. (Sing n) => (PVal) -> (Tm n)
quotep (PVLam n b) = do
  Lam n $ do
    let v' = b (topPVal @n)
    quotep v'
quotep (PVVar h s) = quoteSpp s (lvlVar h)

quoteSpp :: (Sing i) => PSp -> Tm i -> Tm i
quoteSpp PSNil e = e
quoteSpp (PSApp s x) e = App (quoteSpp s e) (quotep x)

nfp :: (Sing j) => PVals i -> Tm i -> (Tm j)
nfp e t = quotep (evalp e t)

-- * Tests

-------------------------------------------------------------------------------

ki :: IO Val
ki = do
  i <- lazilyEval Nil $ Lam "x" $ Var IZ
  k <- lazilyEval Nil $ Lam "x" $ Lam "y" $ Var (IS IZ)
  eval (i :* k :* Nil) $ App (Var (IS IZ)) (Var IZ)

main :: IO ()
main = do
  test <- ki
  test' <- quote @Z test
  return ()

-- print test'
