{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}

module Named.FoilV where
-- From https://github.com/KarinaTyulebaeva/lambda-n-ways/blob/main/lib/Foil/Eager/Foil.hs
-- with Booleans added by SCW
-- also given an applicative semantics by SCW
import Unsafe.Coerce
import System.Exit (exitFailure)
import qualified Util.Syntax.Lambda as LC
import qualified Util.IdInt as IdInt
import qualified Util.Impl as LambdaImpl
import Data.IntMap.Strict
import qualified Data.IntMap.Strict as IntMap
import Control.DeepSeq
import GHC.Generics (Generic)
import Data.IntSet
import qualified Data.IntSet as IntSet
import qualified Data.Maybe
import Data.Kind (Type)

type Id = Int
type RawName = Id
type RawScope = IntSet

data {- kind -} S
  = {- type -} VoidS
  -- | {- type -} Singleton
  -- | {- type -} List

newtype Scope (n :: S) = UnsafeScope RawScope
  deriving newtype NFData
newtype Name (n :: S) = UnsafeName RawName
  deriving newtype (NFData, Eq, Ord)
newtype NameBinder (n :: S) (l :: S) =
  UnsafeNameBinder (Name l)
    deriving newtype (NFData, Eq, Ord)

emptyScope :: Scope VoidS
emptyScope = UnsafeScope IntSet.empty

extendScope :: NameBinder n l -> Scope n -> Scope l
extendScope (UnsafeNameBinder (UnsafeName id)) (UnsafeScope scope) =
  UnsafeScope (IntSet.insert id scope)

rawFreshName :: RawScope -> RawName
rawFreshName scope | IntSet.null scope = 0
                   | otherwise = IntSet.findMax scope + 1

withFreshBinder
  :: Scope n
  -> (forall l. NameBinder n l -> r)
  -> r
withFreshBinder (UnsafeScope scope) cont =
  cont binder
  where
    binder = UnsafeNameBinder (UnsafeName (rawFreshName scope))

nameOf :: NameBinder n l -> Name l
nameOf (UnsafeNameBinder name) = name

rawMember :: RawName -> RawScope -> Bool
rawMember i s = IntSet.member i s

member :: Name l -> Scope n -> Bool
member (UnsafeName name) (UnsafeScope s) = rawMember name s

data Expr n where
  VarE :: {-# UNPACK #-} !(Name n) -> Expr n
  AppE :: !(Expr n) -> !(Expr n) -> Expr n
  LamE :: !(NameBinder n l) -> !(Expr l) -> Expr n
  BoolE :: {-# UNPACK #-} !Bool -> Expr n
  IfE :: !(Expr n) -> !(Expr n) -> !(Expr n) -> Expr n
instance Eq (Expr n) where
  VarE x == VarE y = x == y
  AppE f1 x1 == AppE f2 x2 = (f1 == f2) && (x1 == x2)
  LamE x1 body1 == LamE x2 body2 = (x1 == unsafeCoerce x2) && (unsafeCoerce body1 == body2)
  BoolE b1 == BoolE b2 = b1 == b2
  IfE t1 t2 t3 == IfE u1 u2 u3 = 
    t1 == u1 && t2 == u2 && t3 == u3
  _ == _ = False

instance forall l. NFData (Expr l) where
  rnf (LamE binder body) = rnf binder `seq` rnf body
  rnf (AppE fun arg) = rnf fun `seq` rnf arg
  rnf (VarE name) = rnf name
  rnf (BoolE b) = rnf b
  rnf (IfE a b c) = rnf a `seq` rnf b `seq` rnf c
-- Distinct constraints
class ExtEndo (n :: S)

class (ExtEndo n => ExtEndo l ) => Ext (n:: S) (l :: S)
instance ( ExtEndo n => ExtEndo l ) => Ext n l

class Distinct (n :: S)
instance Distinct VoidS

type DExt n l = (Distinct l, Ext n l)

-- Safer scopes with distinct constraints
data DistinctEvidence ( n :: S) where
  Distinct :: Distinct n => DistinctEvidence n

unsafeDistinct :: DistinctEvidence n
unsafeDistinct = unsafeCoerce (Distinct :: DistinctEvidence VoidS)

data ExtEvidence ( n:: S) ( l :: S) where
  Ext :: Ext n l => ExtEvidence n l

unsafeExt :: ExtEvidence n l
unsafeExt = unsafeCoerce (Ext :: ExtEvidence VoidS VoidS)

withFresh :: Distinct n => Scope n
  -> (forall l . DExt n l => NameBinder n l -> r ) -> r
withFresh scope cont = withFreshBinder scope (\binder ->
  unsafeAssertFresh binder cont)

unsafeAssertFresh :: forall n l n' l' r. NameBinder n l
  -> (DExt n' l' => NameBinder n' l' -> r) -> r
unsafeAssertFresh binder cont =
  case unsafeDistinct @l' of
    Distinct -> case unsafeExt @n' @l' of
      Ext -> cont (unsafeCoerce binder)

withRefreshed :: Distinct o => Scope o -> Name i
  -> (forall o'. DExt o o' => NameBinder o o' -> r) -> r
withRefreshed scope@(UnsafeScope rawScope) name@(UnsafeName id) cont
  | IntSet.member id rawScope = withFresh scope cont
  | otherwise = unsafeAssertFresh (UnsafeNameBinder name) cont

-- generic sinking
concreteSink :: DExt n l => Expr n -> Expr l
concreteSink = unsafeCoerce

class Sinkable (e :: S -> Type) where
  sinkabilityProof :: (Name n -> Name l) -> e n -> e l

instance Sinkable Name where
  sinkabilityProof rename = rename

sink :: (Sinkable e, DExt n l) => e n -> e l
sink = unsafeCoerce

instance Sinkable Expr where
  sinkabilityProof rename (VarE v) = VarE (rename v)
  sinkabilityProof rename (AppE f e) = AppE (sinkabilityProof rename f) (sinkabilityProof rename e)
  sinkabilityProof rename (LamE binder body) = extendRenaming rename binder \rename' binder' ->
    LamE binder' (sinkabilityProof rename' body)
  sinkabilityProof rename (BoolE b) = BoolE b
  sinkabilityProof rename (IfE a b c) = 
    IfE (sinkabilityProof rename a) 
        (sinkabilityProof rename b)
        (sinkabilityProof rename b)

extendRenaming :: (Name n -> Name n') -> NameBinder n l
  -> (forall l'. (Name l -> Name l') -> NameBinder n' l' -> r ) -> r
extendRenaming _ (UnsafeNameBinder name) cont =
  cont unsafeCoerce (UnsafeNameBinder name)

-- Substitution
newtype Substitution (e :: S -> Type) (i :: S) (o :: S) =
  UnsafeSubstitution (IntMap (e o))

class HasVar (e :: S -> Type) where
  makeVar :: Name n -> e n

lookupSubst :: HasVar e => Substitution e i o -> Name i -> e o
lookupSubst !(UnsafeSubstitution env) (UnsafeName id) =
    case IntMap.lookup id env of
        Just ex -> ex
        Nothing -> makeVar (UnsafeName id)

identitySubst :: Substitution e i i
identitySubst = UnsafeSubstitution IntMap.empty

addSubst :: Substitution e i o -> NameBinder i i' -> e o -> Substitution e i' o
addSubst !(UnsafeSubstitution env) (UnsafeNameBinder (UnsafeName id)) ex = UnsafeSubstitution (IntMap.insert id ex env)

addRename :: HasVar e => Substitution e i o -> NameBinder i i' -> Name o -> Substitution e i' o
addRename !s@(UnsafeSubstitution env) b@(UnsafeNameBinder (UnsafeName name1)) n@(UnsafeName name2)
    | name1 == name2 = UnsafeSubstitution (IntMap.delete name1 env)
    | otherwise = addSubst s b (makeVar n)

instance (Sinkable e) => Sinkable (Substitution e i) where
  sinkabilityProof rename (UnsafeSubstitution env) =
    UnsafeSubstitution (fmap (sinkabilityProof rename) env)

instance HasVar Expr where
  makeVar = VarE

-- Substitute part
substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute !scope !subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> (AppE $! (substitute scope subst f)) $! (substitute scope subst x)
    LamE binder body -> withRefreshed scope (nameOf binder) (\binder' ->
        let !subst' = addRename (sink subst) binder (nameOf binder')
            !scope' = extendScope binder' scope
            !body' = substitute scope' subst' body in LamE binder' body'
        )
    BoolE b -> BoolE b
    IfE x y z  -> ((IfE $! (substitute scope subst x))
                        $! (substitute scope subst y))
                        $! (substitute scope subst z)
whnf :: Distinct n => Scope n -> Expr n -> Expr n
whnf !scope = \case
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst =  addSubst identitySubst binder $! (whnf scope arg)
        in whnf scope $! (substitute scope subst body)
      fun' -> AppE fun' arg
  IfE scrut tru fls ->
    case whnf scope scrut of
      BoolE True -> whnf scope tru
      BoolE False -> whnf scope fls
      sc' -> IfE sc' tru fls
  t -> t

nf :: Distinct n => Scope n -> Expr n -> Expr n
nf !scope expr = case expr of
  LamE binder body -> unsafeAssertFresh binder \binder' ->
          let !scope' = extendScope binder' scope
        in LamE binder' (nf scope' body)
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let !subst = addSubst identitySubst binder $! (whnf scope arg)
        in nf scope $! (substitute scope subst body)
      fun' -> AppE (nf scope fun') (nf scope arg)
  IfE scrut tru fls ->
    case whnf scope scrut of
      BoolE True -> whnf scope tru
      BoolE False -> whnf scope fls
      sc' -> IfE sc' tru fls 
  t -> t

nf_cbv :: Distinct n => Scope n -> Expr n -> Expr n
nf_cbv !scope expr = case expr of
  -- LamE binder body -> unsafeAssertFresh binder \binder' ->
  --         let scope' = extendScope binder' scope
  --       in LamE binder' (nf_cbv scope' body)
  AppE fun arg -> do
    let !fun' = nf_cbv scope fun
        !arg' = nf_cbv scope arg
    case fun' of
      LamE binder body ->
        let subst =  addSubst identitySubst binder arg'
        in nf_cbv scope (substitute scope subst body)
      fun' -> AppE fun' arg'
  IfE scrut tru fls ->
    case whnf scope scrut of
      BoolE True -> whnf scope tru
      BoolE False -> whnf scope fls
      sc' -> IfE sc' tru fls 
  t -> t

nfd :: Expr VoidS -> Expr VoidS
nfd term = nf emptyScope term

toLambdaPi :: Distinct n => Scope n -> IntMap (Name n) -> LC.LC IdInt.IdInt -> Expr n
toLambdaPi !scope !env = \case
  LC.Var (IdInt.IdInt x) ->
    case IntMap.lookup x env of
      Just name -> VarE name
      Nothing -> error ("unbound variable: " ++ show x)
  LC.App fun arg ->
    (AppE (toLambdaPi scope env fun)) (toLambdaPi scope env arg)

  LC.Lam (IdInt.IdInt x) body -> withFresh scope $ \binder ->
    let !scope' = extendScope binder scope
        !env' = IntMap.insert x (nameOf binder) (sink <$> env)
    in LamE binder (toLambdaPi scope' env' body)
  LC.Bool b      -> BoolE b
  LC.If t1 t2 t3 -> IfE (toLambdaPi scope env t1) 
                        (toLambdaPi scope env t2) 
                        (toLambdaPi scope env t3)


fromLC :: LC.LC IdInt.IdInt -> Expr VoidS
fromLC = toLambdaPi emptyScope IntMap.empty

toLC :: Expr n -> LC.LC IdInt.IdInt
toLC = \case
    VarE (UnsafeName id) -> LC.Var (IdInt.IdInt id)
    AppE fun arg -> LC.App (toLC fun) (toLC arg)
    LamE binder body ->
      let UnsafeName id = nameOf binder
      in LC.Lam (IdInt.IdInt id) (toLC body)
    BoolE b -> LC.Bool b
    IfE x y z -> LC.If (toLC x) (toLC y) (toLC z)

unsafeEquals :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeEquals (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 == name2

unsafeLess :: NameBinder n l -> NameBinder n1 l1 -> Bool
unsafeLess (UnsafeNameBinder (UnsafeName name1)) (UnsafeNameBinder (UnsafeName name2)) = name1 < name2

-- Unsafe renaming of a raw name
unsafeRenameVar :: IntMap RawName -> RawName -> RawName
unsafeRenameVar subst name1 = case IntMap.lookup name1 subst of
  Just name2 -> name2
  Nothing -> name1

unsafeAeq
  :: IntMap RawName
  -> IntMap RawName
  -> IntSet
  -> IntSet
  -> Expr n
  -> Expr l
  -> Bool
unsafeAeq !subst1 !subst2 !target1 !target2 (VarE (UnsafeName x)) (VarE (UnsafeName y))
  | IntSet.member x target1 = False
  | IntSet.member y target2 = False
  | otherwise = (unsafeRenameVar subst1 x) == (unsafeRenameVar subst2 y)
unsafeAeq !subst1 !subst2 !target1 !target2 (AppE fun1 arg1) (AppE fun2 arg2)
  = and
    [ unsafeAeq subst1 subst2 target1 target2 fun1 fun2
    , unsafeAeq subst1 subst2 target1 target2 arg1 arg2 ]
unsafeAeq !subst1 !subst2 !target1 !target2
  (LamE binder1@(UnsafeNameBinder (UnsafeName name1)) body1)
  (LamE binder2@(UnsafeNameBinder (UnsafeName name2)) body2)
  | unsafeEquals binder1 binder2 = unsafeAeq subst1 subst2 target1 target2 body1 body2
  | unsafeLess binder1 binder2 =
        let subst2' = IntMap.insert name2 name1 subst2
            target2' = IntSet.insert name1 target2
        in unsafeAeq subst1 subst2' target1 target2' body1 body2
  | otherwise =
        let (UnsafeName name1) = nameOf binder1
            subst1' = IntMap.insert name1 name2 subst1
            target1' = IntSet.insert name2 target1
        in unsafeAeq subst1' subst2 target1' target2 body1 body2
unsafeAeq subst1 subst2 target1 target2 (BoolE b1) (BoolE b2) = b1 == b2
unsafeAeq subst1 subst2 target1 target2 (IfE t1 t2 t3) (IfE t1' t2' t3') =
     and
      [ unsafeAeq subst1 subst2 target1 target2 t1 t1'
      , unsafeAeq subst1 subst2 target1 target2 t2 t2'
      , unsafeAeq subst1 subst2 target1 target2 t3 t3' ] 
unsafeAeq _ _ _ _ _ _ = False

aeq_impl :: Expr n -> Expr n -> Bool
aeq_impl = (==) -- unsafeAeq IntMap.empty IntMap.empty IntSet.empty IntSet.empty

impl :: LambdaImpl.LambdaImpl
impl =
  LambdaImpl.LambdaImpl
    { LambdaImpl.impl_name = "Named.FoilV",
      LambdaImpl.impl_fromLC = fromLC,
      LambdaImpl.impl_toLC = toLC,
      LambdaImpl.impl_nf = nfd,
      LambdaImpl.impl_nfi = error "nfi unimplemented",
      LambdaImpl.impl_aeq = aeq_impl,
      LambdaImpl.impl_eval = whnf emptyScope
    }