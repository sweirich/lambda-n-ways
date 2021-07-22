{-# language CPP #-}
{-# language AllowAmbiguousTypes #-}
{-# language BangPatterns #-}
{-# language BlockArguments #-}
{-# language ConstraintKinds #-}
{-# language DataKinds #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
-- {-# language ImpredicativeTypes #-}
-- {-# language ImportQualifiedPost #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language PatternSynonyms #-}
{-# language PolyKinds #-}
{-# language QuantifiedConstraints #-}
{-# language QuasiQuotes #-}
{-# language RankNTypes #-}
{-# language RoleAnnotations #-}
{-# language ScopedTypeVariables #-}
-- {-# language StandaloneKindSignatures #-}
{-# language TemplateHaskell #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language UndecidableInstances #-}
{-# language Unsafe #-}
{-# language ViewPatterns #-}
{-# OPTIONS_HADDOCK not-home #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-} -- go home, ghc, you're drunk

-- |
-- Copyright :  (c) Edward Kmett 2020
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable

-- This is Data.Type.Internal from 
-- https://github.com/ekmett/haskell/blob/master/types/src/Data/Type/Internal.hs
-- adapted by SCW to compile without StandaloneKindSignatures and ImportQualifiedPost

module Kmett.Type where

import Control.Applicative
import Control.Concurrent
import Data.Constraint
import Data.Function
import Data.GADT.Compare
import Data.IORef
import Data.Int
import Data.Hashable
import Data.Kind
import qualified Data.List.NonEmpty as NE
import Data.Proxy
import Data.STRef
import Data.Some
import Data.Traversable
import Data.Type.Equality
import Data.Void
import Data.Word
import Foreign.Ptr
import Foreign.StablePtr
import GHC.Exts hiding (the)
import GHC.TypeLits as TL
import GHC.TypeNats as TN
import qualified Language.Haskell.TH as TH
import Numeric.Natural
import Text.Read hiding (Symbol)
import Type.Reflection
import Unsafe.Coerce

-- | You know, just to be a little safer.
unsafeCoerce1 :: forall f a b. f a -> f b
unsafeCoerce1 = unsafeCoerce

--------------------------------------------------------------------------------
-- * Structural Equality
--------------------------------------------------------------------------------

-- | A type with structural equality
--
-- @
-- x '==' y ==> f x '==' f y
-- @
--type StrictEq :: Type -> Constraint
type role StrictEq nominal

class Eq a => StrictEq a
instance StrictEq (MVar a)
instance StrictEq (IORef a)
instance StrictEq (STRef s a)
instance StrictEq (Proxy a)
instance StrictEq ThreadId
instance StrictEq a => StrictEq (Const a b)
instance StrictEq Bool
instance StrictEq ()
instance StrictEq Void
instance StrictEq (Dict p)
instance StrictEq (p :- q)
instance StrictEq Ordering
instance StrictEq a => StrictEq (Maybe a)
instance (StrictEq a, StrictEq b) => StrictEq (a, b)
instance (StrictEq a, StrictEq b, StrictEq c) => StrictEq (a, b, c)
instance (StrictEq a, StrictEq b, StrictEq c, StrictEq d) => StrictEq (a, b, c, d)
instance (StrictEq a, StrictEq b, StrictEq c, StrictEq d, StrictEq e) => StrictEq (a, b, c, d, e)
instance (StrictEq a, StrictEq b) => StrictEq (Either a b)
instance StrictEq a => StrictEq [a]
instance StrictEq a => StrictEq (NE.NonEmpty a)
instance StrictEq (Ptr a)
instance StrictEq Symbol
instance StrictEq Nat
instance StrictEq (StablePtr a)

--------------------------------------------------------------------------------
-- * Singletons
--------------------------------------------------------------------------------

{-
type Sing :: forall k j. k -> j
type family Sing (p :: k) where
  Sing p = p -- makes us too strict in our arguments
  Sing p = SingT p
  Sing p = SingI p
-}

--type Sing :: forall k j. k -> j
type family Sing :: k -> j
type instance Sing = SingT
type instance Sing = SingI

--type SingT :: forall k. k -> Type
type role SingT nominal
newtype SingT (a :: k) = SING { the :: k }
  deriving Hashable

instance (Typeable k, Show k) => Show (SingT (a :: k)) where
  showsPrec d (Sing k) = showParen (d > 10) $
    showString "Sing @" . showsPrec 11 (typeRep @k) . showChar ' ' . showsPrec 11 k

pattern Sing :: k -> SingT (a :: k)
pattern Sing x <- (SING x)

{-# complete Sing :: SingT #-}

instance Eq (SingT a) where
  _ == _ = True

instance Ord (SingT a) where
  compare _ _ = EQ

instance StrictEq (SingT a)


instance StrictEq k => GEq (SingT @k) where
  geq = testEquality

instance (StrictEq k, Ord k) => GCompare (SingT @k) where
  gcompare (Sing i) (Sing j) = case compare i j of
    LT -> GLT
    EQ -> unsafeCoerce1 GEQ
    GT -> GGT


-- assumes equality is structural.
instance StrictEq k => TestEquality (SingT @k) where
  testEquality (Sing i) (Sing j)
    | i == j = Just (unsafeCoerce1 Refl)
    | otherwise = Nothing

--------------------------------------------------------------------------------
-- * Reflection
--------------------------------------------------------------------------------

--type SingI :: forall k. k -> Constraint
class SingI (a :: k) where
  sing :: SingT a

-- bootstrapping singleton singletons
instance Sing k => SingI @(SingT k) ('SING a) where
  sing = SING sing

--type Wrap :: forall k. k -> Type -> Type
#ifdef USE_MAGICDICT
data Wrap (s :: k) (r :: Type) = Wrap (Sing s => Proxy# s -> r)
withSing# :: (Sing a => Proxy# a -> r) -> Sing a -> Proxy# a -> r
withSing# f x y = magicDict (Wrap f) x y
#else
newtype Wrap s r = Wrap (Sing s => Proxy# s -> r)
withSing# :: (Sing a => Proxy# a -> r) -> Sing a -> Proxy# a -> r
withSing# f x y = unsafeCoerce (Wrap f) x y
{-# inline withSing# #-}
#endif

withSing :: Sing a -> (Sing a => r) -> r
withSing s r = withSing# (\_ -> r) s proxy#

reify :: k -> (forall (a::k). Sing a => Proxy# a -> r) -> r
reify k f = withSing# f (SING k) proxy#

reflect :: forall k (a::k). Sing a => k
reflect = the (sing @k @a)

reflect# :: forall k (a::k). Sing a => Proxy# a -> k
reflect# _ = the (sing @k @a)

data family Me# :: k
type family Me :: k
type instance Me = 'SING Me
type instance Me = '()
type instance Me = 'Proxy
type instance Me = 'Const Me
type instance Me = '(Me,Me)
type instance Me = '(Me,Me,Me)
type instance Me = '(Me,Me,Me,Me)
type instance Me = '(Me,Me,Me,Me,Me)
type instance Me = '(Me,Me,Me,Me,Me,Me)
type instance Me = '(Me,Me,Me,Me,Me,Me,Me)
type instance Me = '(Me,Me,Me,Me,Me,Me,Me,Me)
type instance Me = '(Me,Me,Me,Me,Me,Me,Me,Me,Me)
type instance Me = 'Refl
type instance Me = 'HRefl
type instance Me = Me# :: Dict p
type instance Me = Me# :: p :- q

type Singular k = Sing @k Me

me :: forall k. Singular k => k
me = reflect @k @Me

--------------------------------------------------------------------------------
-- * Lowering Constraint
--------------------------------------------------------------------------------

type Constraint' = Some Dict

toConstraint :: Constraint' -> Constraint
toConstraint = unsafeCoerce

fromConstraint :: Constraint -> Constraint'
fromConstraint = unsafeCoerce

instance Show Constraint where
  showsPrec d _ = showParen (d > 10) $
    showString "Constraint Dict"

pattern Constraint :: Dict p -> Constraint
pattern Constraint t <- (fromConstraint -> Some t) where
  Constraint t = toConstraint (Some t)

--type SConstraint# :: Constraint -> Type
data SConstraint# (p :: Constraint) where
  SConstraint# :: Dict p -> SConstraint# p

upSConstraint# :: Sing p -> SConstraint# p
upSConstraint# (Sing (Constraint t)) = unsafeCoerce1 (SConstraint# t)

pattern SConstraintDict :: Dict p -> Sing p
pattern SConstraintDict t <- (upSConstraint# -> SConstraint# t) where
  SConstraintDict t = SING $ Constraint t

pattern SConstraint :: () => p => Sing p
pattern SConstraint = SConstraintDict Dict

instance p => SingI p where
  sing = SConstraint

--------------------------------------------------------------------------------
-- * Dict itself as a kind
--------------------------------------------------------------------------------

-- should be handleable by template-haskell with very minor changes
--type SDict# :: forall p. Dict p -> Type
type role SDict# nominal
data SDict# (t :: Dict p) where
  SMkDict# :: p => SDict# (MkDict :: Dict p)
           -- ^- gather context from constructor, pass it along

upSDict# :: forall (p :: Constraint) (a :: Dict p). Sing a -> SDict# a
upSDict# (Sing Dict) = unsafeCoerce1 (SMkDict# @p)

pattern SDict
  :: forall (p::Constraint) (r::Dict p).
  () =>
  (p, r ~ MkDict) => Sing r
-- ^- and pass it out here
pattern SDict <- (upSDict# -> SMkDict#) where
  SDict = SING Dict

type MkDict = Me# :: Dict p
instance (p, r ~ MkDict) => SingI @(Dict p) r where
  sing = SDict

--------------------------------------------------------------------------------
-- * p :- q
--------------------------------------------------------------------------------

--type MkImpl :: p :- q
type MkImpl = (Me# :: p :- q)
type instance Me = MkImpl
instance (p => q, r ~ MkImpl) => SingI @(p :- q) r where
  sing = SING $ Sub Dict

-- anything but
--type SImpl# :: forall p q. (p :- q) -> Type
type role SImpl# nominal
data SImpl# (t :: p :- q) where
  SImpl# :: (p => q) => SImpl# (MkImpl :: (p :- q))

upSImpl# :: Sing a -> SImpl# a
upSImpl# (Sing (x :: (p :- q))) = unsafeCoerce1 (quack x (SImpl# @p @q))
newtype Quack p q r = Quack ((p => q) => r)
quack :: forall p q r. (p :- q) -> ((p => q) => r) -> r
quack p r = unsafeCoerce (Quack @p @q @r r) (mapC p) where
  mapC :: (p :- q) -> Sing p -> Sing q
  mapC x SConstraint = case x of
    Sub Dict -> SConstraint

pattern SImpl :: () => (p => q, r ~ MkImpl) => Sing @(p :- q) r
pattern SImpl <- (upSImpl# -> SImpl#) where
  SImpl = SING (Sub Dict)

--------------------------------------------------------------------------------
-- * Lowering Types
--------------------------------------------------------------------------------

type Type' = Some (TypeRep :: Type -> Type)

toType :: Type' -> Type
toType = unsafeCoerce

fromType :: Type -> Type'
fromType = unsafeCoerce

instance Show Type where
  showsPrec d (Type t) = showsPrec d t

instance Eq Type where
  (==) = (==) `on` fromType

instance StrictEq Type

pattern Type :: TypeRep (a :: Type) -> Type
pattern Type t <- (fromType -> Some t) where
  Type t = toType (Some t)

instance Typeable a => SingI (a :: Type) where
  sing = SING $ Type $ typeRep @a

--type SType' :: Type -> Type
data SType' (a :: Type) where
  SType' :: TypeRep a -> SType' (a :: Type)

upSType :: Sing a -> SType' a
upSType (Sing (Type t)) = unsafeCoerce1 (SType' t)

pattern SType :: TypeRep a -> Sing (a :: Type)
pattern SType t <- (upSType -> SType' t) where
  SType t = SING $ Type t

--------------------------------------------------------------------------------
-- * Lowering Nats
--------------------------------------------------------------------------------

instance KnownNat a => SingI @Nat a where
  sing = SING $ Nat $ TN.natVal (Proxy @a)

instance Show Nat where
  showsPrec d = showsPrec d . fromNat

instance Eq Nat where
  (==) = (==) `on` fromNat

instance Ord Nat where
  compare = compare `on` fromNat

instance Read Nat where
  readPrec = Nat <$> readPrec

toNat :: Natural -> Nat
toNat = unsafeCoerce

fromNat :: Nat -> Natural
fromNat = unsafeCoerce

liftN2 :: (Natural -> Natural -> Natural) -> Nat -> Nat -> Nat
liftN2 f x y = Nat $ f (fromNat x) (fromNat y)

liftN :: (Natural -> Natural) -> Nat -> Nat
liftN f = Nat . f . fromNat

instance Num Nat where
  (+) = liftN2 (+)
  (-) = liftN2 (-)
  (*) = liftN2 (*)
  abs = liftN abs
  signum = liftN signum
  negate = liftN negate
  fromInteger = Nat . fromInteger

instance Enum Nat where
  succ = liftN succ
  pred = liftN pred
  toEnum = Nat . toEnum
  fromEnum = fromEnum . fromNat
  enumFrom = fmap Nat . enumFrom . fromNat
  enumFromTo (Nat n) (Nat m) = Nat <$> enumFromTo n m
  enumFromThen (Nat n) (Nat m) = Nat <$> enumFromThen n m
  enumFromThenTo (Nat n) (Nat m) (Nat o) = Nat <$> enumFromThenTo n m o

instance Real Nat where
  toRational = toRational . fromNat

instance Integral Nat where
  quot = liftN2 quot
  rem = liftN2 rem
  div = liftN2 rem
  mod = liftN2 rem
  quotRem (Nat n) (Nat m) = case quotRem n m of
    (q,r) -> (Nat q, Nat r)
  divMod (Nat n) (Nat m) = case divMod n m of
    (q,r) -> (Nat q, Nat r)
  toInteger = toInteger . fromNat

pattern Nat :: Natural -> Nat
pattern Nat n <- (fromNat -> n) where
  Nat n = toNat n

{-# complete Nat #-}

-----------------------------------------------------------------------------
-- * Integral types
-----------------------------------------------------------------------------

pattern Z :: Integral a => a
pattern Z = 0

pattern S :: Integral a => a -> a
pattern S n <- ((\case 0 -> Nothing; n -> Just $ n-1) -> Just n)
  where S n = n+1

{-# complete Z, S :: Natural #-}
{-# complete Z, S :: Nat #-}
{-# complete Z, S :: Int #-}
{-# complete Z, S :: Int8 #-}
{-# complete Z, S :: Int16 #-}
{-# complete Z, S :: Int32 #-}
{-# complete Z, S :: Int64 #-}
{-# complete Z, S :: IntPtr #-}
{-# complete Z, S :: Word #-}
{-# complete Z, S :: Word8 #-}
{-# complete Z, S :: Word16 #-}
{-# complete Z, S :: Word32 #-}
{-# complete Z, S :: Word64 #-}
{-# complete Z, S :: WordPtr #-}

--type Z# :: forall k. k
data family Z# :: k
--type S# :: forall k. k -> k
data family S# :: k -> k

class (Integral a, (Z::a) ~ NiceZ) => Nice a where
  type NiceZ :: a
  type NiceS :: a -> a
  sinj :: forall (n::a). Proxy# n -> S n :~: NiceS n

--type Z :: forall k. k
type family Z :: k where
  Z = 0
  Z = NiceZ

--type S :: forall k. k -> k
type family S (n::k) :: k where
  S n = 1 + n
  S n = NiceS n

concat <$> for
  [ ''Natural -- when GHC makes 'Natural' = 'Nat' this will not be 'Nice'
  , ''Integer
  , ''Int, ''Int8, ''Int16, ''Int32, ''Int64, ''IntPtr
  , ''Word, ''Word8, ''Word16, ''Word32, ''Word64, ''WordPtr
  ] \(TH.conT -> n) ->
  [d|
    instance Nice $(n) where
      type NiceZ = Z# @ $(n)
      type NiceS = S# @ $(n)
      sinj _ = Refl
    instance Sing n => SingI (S# @ $(n) n) where sing = SS sing
    instance SingI (Z# @ $(n)) where sing = SZ
    |]

--type SIntegral# :: forall a. a -> Type
data SIntegral# (n :: a) where
  SZ# :: SIntegral# Z
  SS# :: Sing n -> SIntegral# (S n)

upSIntegral :: forall a (n::a). Integral a => Sing n -> SIntegral# n
upSIntegral (SING 0) = unsafeCoerce1 SZ#
upSIntegral (SING n) = unsafeCoerce1 $ SS# (SING (n-1))

-- shared for both injective types and for Nat

pattern SZ :: forall a (n::a). Integral a => n ~ Z => Sing n
pattern SZ <- (upSIntegral -> SZ#) where
  SZ = SING 0

pattern SS :: forall a (n::a). Integral a => forall (n'::a). n ~ S n' => Sing n' -> Sing n
pattern SS n <- (upSIntegral -> SS# n) where
  SS (Sing n) = SING (S n)

--type SIntegral'# :: forall a. a -> Type
data SIntegral'# (n :: a) where
  SZ'# :: SIntegral'# Z
  SS'# :: Sing n -> SIntegral'# (NiceS n)

upSIntegral' :: forall a (n::a). Nice a => Sing n -> SIntegral'# n
upSIntegral' (SING 0) = unsafeCoerce1 SZ'#
upSIntegral' (SING n) = unsafeCoerce1 $ SS'# (SING (n-1))

-- nicer pattern that atually learns something for nice numerics
-- SCW: figure out this type error
{-
pattern SS' :: forall a (n::a). Nice a => forall (n'::a). n ~ NiceS n' => Sing n' -> Sing n
pattern SS' n <- (upSIntegral' -> SS'# n) where
 SS' (Sing n) = SING $ case sinj (proxy# @n) of 
   Refl -> S n
-}

{-# complete SS, SZ #-}
-- {-# complete SS', SZ #-}

--------------------------------------------------------------------------------
-- * Lifting Dict and types that are otherwise singleton
--------------------------------------------------------------------------------

-- used to fill in 'Me' when the singular term can't be lifted

--------------------------------------------------------------------------------
-- * Lifting (Ptr a)
--------------------------------------------------------------------------------

data family FromWordPtr# :: WordPtr -> k

--type MkPtr :: forall a. WordPtr -> Ptr a
type MkPtr = (FromWordPtr# :: WordPtr -> Ptr a)

instance Sing n => SingI (MkPtr n) where
  sing = SMkPtr sing

pattern SMkPtr :: Sing n -> Sing (MkPtr n)
pattern SMkPtr n <- Sing (SING . ptrToWordPtr -> n) where
  SMkPtr (Sing n) = SING $ wordPtrToPtr n

{-# complete SMkPtr #-}

--------------------------------------------------------------------------------
-- * Lifting (StablePtr a)
--------------------------------------------------------------------------------

data family FromPtr# :: Ptr a -> k

--type MkStablePtr :: forall a. Ptr () -> StablePtr a
type MkStablePtr = (FromPtr# :: Ptr () -> StablePtr a)

instance Sing n => SingI (MkStablePtr n) where
  sing = SMkStablePtr sing

pattern SMkStablePtr :: Sing n -> Sing (MkStablePtr n)
pattern SMkStablePtr n <- Sing (SING . castStablePtrToPtr -> n) where
  SMkStablePtr (Sing n) = SING $ castPtrToStablePtr n

{-# complete SMkStablePtr #-}

--------------------------------------------------------------------------------
-- * Lifting Char
--------------------------------------------------------------------------------

data family FromSymbol :: Symbol -> k

--type MkChar :: Symbol -> Char
type MkChar = (FromSymbol :: Symbol -> Char)

instance KnownSymbol s => SingI (MkChar s) where
  sing = case symbolVal $ Proxy @s of
    [c] -> SING c
    _ -> error "SChar.sing: bad argument"

--------------------------------------------------------------------------------
-- * Lowering Symbol
--------------------------------------------------------------------------------

toSymbol :: String -> Symbol
toSymbol = unsafeCoerce

fromSymbol :: Symbol -> String
fromSymbol = unsafeCoerce

pattern Symbol :: String -> Symbol
pattern Symbol s <- (fromSymbol -> s) where
  Symbol s = toSymbol s

{-# complete Symbol #-}

instance Eq Symbol where
  (==) = (==) `on` fromSymbol

instance Ord Symbol where
  compare = compare `on` fromSymbol

instance Show Symbol where
  showsPrec d = showsPrec d . fromSymbol

instance Read Symbol where
  readPrec = Symbol <$> readPrec

instance IsList Symbol where
  type Item Symbol = Char
  fromList = Symbol . fromList
  fromListN n xs = Symbol (fromListN n xs)
  toList = toList . fromSymbol

instance IsString Symbol where
  fromString = toSymbol

instance KnownSymbol s => SingI s where
  sing = SING $ Symbol $ symbolVal $ Proxy @s