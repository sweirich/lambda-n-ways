{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# OPTIONS  -Wall -fno-warn-unticked-promoted-constructors  #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

{-

This implementation is derived from Allais et al. below but modified to
represent the untyped lambda calculus. It is similar to the DeBruijn.Par
implementations and probably could be optimized in a similar way. The focus of
the original paper is on proofs, so it is not clear that this is an
appropriate implementation for execution.

Type-and-Scope Safe Programs and Their Proofs
Guillaume Allais, James Chapman, Conor McBride, James McKinna
-}

module DeBruijn.Kit (impl) where

import Control.DeepSeq
import Control.Monad.State
import Data.Bifunctor (second)
import Data.Maybe (fromJust)
import IdInt
import Impl
import Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Kit",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nfd,
      impl_nfi = error "NFI unimplemented",
      impl_aeq = (==)
    }

-- A context is a natural number representing the scope depth
data Nat = Z | S Nat

data SNat n where
  SZ :: SNat 'Z
  SS :: SNat a -> SNat ('S a)

type Con = Nat

type SCon = SNat

-- A variable is a fancy de Bruijn index
data Var :: Nat -> * where
  VZ :: Var ('S a)
  VS :: Var a -> Var ('S a)

data Term :: Nat -> * where
  TeVar :: Var g -> Term g
  TeLam :: Term ('S g) -> Term g
  TeApp :: Term g -> Term g -> Term g

instance NFData (Var a) where
  rnf VZ = ()
  rnf (VS a) = rnf a

instance NFData (Term a) where
  rnf (TeVar i) = rnf i
  rnf (TeLam d) = rnf d
  rnf (TeApp a b) = rnf a `seq` rnf b

instance Eq (Var n) where
  VZ == VZ = True
  (VS x) == (VS y) = x == y
  _ == _ = False

instance Eq (Term n) where
  TeVar x == TeVar y = x == y
  TeLam x == TeLam y = x == y
  TeApp x1 x2 == TeApp y1 y2 = x1 == y1 && x2 == y2
  _ == _ = False

-- An (evaluation) environment is a collection of environment
-- values covering a given context `g`.

type Environment (d :: Con) (e :: Con -> *) (g :: Con) =
  Var g -> e d

envNull :: Environment d e 'Z
envNull v = case v of

envCons :: Environment d e g -> e d -> Environment d e ('S g)
envCons _ e VZ = e
envCons env _ (VS v) = env v

type Included g d = Environment d Var g

refl :: forall g. Included g g
refl = id

top :: forall d g. Included g d -> Included g ('S d)
top inc = VS . inc

{-
pop :: forall d g. Included g d -> Included ('S g) ('S d)
pop _   VZ     = VZ
pop inc (VS v) = VS $ inc v

trans :: Included g h -> Included h i -> Included g i
trans inc1 inc2 = inc2 . inc1
-}

data Semantics (e :: Con -> *) (m :: Con -> *) = Semantics
  { weak :: forall g d. Included g d -> e g -> e d,
    embed :: forall g. Var g -> e g,
    var :: forall g. e g -> m g,
    app :: forall g. m g -> m g -> m g,
    lam :: forall g. (forall d. Included g d -> e d -> m d) -> m g
  }

wkEnv ::
  forall h d g e m.
  Semantics e m ->
  Included d h ->
  Environment d e g ->
  Environment h e g
wkEnv Semantics {..} inc env v = weak inc $ env v

semanticsTerm ::
  forall e m d g.
  Semantics e m ->
  Term g ->
  Environment d e g ->
  m d
semanticsTerm sem@Semantics {..} = go
  where
    go :: forall d' g'. Term g' -> Environment d' e g' -> m d'
    go (TeVar v) env = var $ env v
    go (TeLam t) env = lam $ \inc v -> go t (envCons (wkEnv sem inc env) v)
    go (TeApp f t) env = app (go f env) (go t env)

evalTerm :: forall e m g. Semantics e m -> SCon g -> Term g -> m g
evalTerm sem@Semantics {..} g t = semanticsTerm sem t (env g)
  where
    env :: forall g'. SCon g' -> Environment g' e g'
    env SZ = envNull
    env (SS sg) = envCons (wkEnv sem (top refl) $ env sg) (embed VZ)

------------------------------------------------------------------------
-- Syntactic Semantics
------------------------------------------------------------------------

renaming :: Semantics Var Term
renaming =
  Semantics
    { weak = \inc v -> inc v,
      embed = id,
      var = TeVar,
      app = TeApp,
      lam = \t -> TeLam $ t (top refl) VZ
    }

weakTe :: Included g d -> Term g -> Term d
weakTe inc t = semanticsTerm renaming t inc

type Subst g d = Environment d Term g

substitution :: Semantics Term Term
substitution =
  Semantics
    { weak = weakTe,
      embed = TeVar,
      var = id,
      app = TeApp,
      lam = \t -> TeLam $ t (top refl) (TeVar VZ)
    }

substTe :: Subst g d -> Term g -> Term d
substTe sub t = semanticsTerm substitution t sub

singleSub :: Term g -> Subst (S g) g
singleSub a VZ = a
singleSub a (VS m) = TeVar m

------------------------------------------------------------------------
-- Pretty Printing Semantics
------------------------------------------------------------------------

newtype Constant k (g :: Con) = Constant {runConstant :: k}

prettyPrinting :: Semantics (Constant String) (Constant (State [String] String))
prettyPrinting =
  Semantics
    { weak = \_ -> Constant . runConstant,
      embed = Constant . show . deBruijn,
      var = Constant . return . runConstant,
      app = \mf mt ->
        Constant $ do
          f <- runConstant mf
          t <- runConstant mt
          return $ f ++ " (" ++ t ++ ")",
      lam = \mbody -> Constant $ do
        ys <- get
        let (x : xs) = ys
        () <- put xs
        body <- runConstant $ mbody (top refl) (Constant x)
        return $ '\\' : x ++ ". " ++ body
    }

deBruijn :: forall g. Var g -> Integer
deBruijn VZ = 0
deBruijn (VS v) = 1 + deBruijn v

prettyPrint :: forall g. SCon g -> Term g -> String
prettyPrint g t = evalState (runConstant $ evalTerm prettyPrinting g t) names
  where
    names = fmap (: []) alpha ++ alphaInt
    alpha = ['a' .. 'z']
    alphaInt = concatMap (\i -> fmap (: show i) alpha) [(0 :: Integer) ..]

toLCsem :: Semantics (Constant (LC IdInt)) (Constant (State [IdInt] (LC IdInt)))
toLCsem =
  Semantics
    { weak = \_ -> Constant . runConstant,
      embed = Constant . Var . IdInt . fromInteger . deBruijn,
      var = Constant . return . runConstant,
      app = \mf mt ->
        Constant $ do
          f <- runConstant mf
          t <- runConstant mt
          return $ App f t,
      lam = \mbody -> Constant $ do
        ys <- get
        let (x : xs) = (ys :: [IdInt])
        () <- put xs
        body <- runConstant $ mbody (top refl) (Constant (Var x))
        return $ Lam x body
    }

toLC :: Term Z -> LC IdInt
toLC t = evalState (runConstant $ evalTerm toLCsem SZ t) names
  where
    names :: [IdInt]
    names = [firstBoundId ..]

fromLC :: LC IdInt -> Term Z
fromLC = to []
  where
    to :: [(IdInt, Var n)] -> LC IdInt -> Term n
    to vs (Var v) = TeVar (fromJust (lookup v vs))
    to vs (Lam v b) = TeLam b'
      where
        b' = to ((v, VZ) : mapSnd VS vs) b
    to vs (App f a) = TeApp (to vs f) (to vs a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (second f)

------------------------------------------------------------------------
-- Benchmark normalization function ?
------------------------------------------------------------------------

nfd :: Term n -> Term n
nfd e@(TeVar _) = e
nfd (TeLam b) = TeLam (nfd b)
nfd (TeApp f a) =
  case whnf f of
    TeLam b -> nfd (instantiate b a)
    f' -> TeApp (nfd f') (nfd a)

whnf :: Term n -> Term n
whnf e@(TeVar _) = e
whnf e@(TeLam _) = e
whnf (TeApp f a) =
  case whnf f of
    TeLam b -> whnf (instantiate b a)
    f' -> TeApp f' a

instantiate :: Term (S n) -> Term n -> Term n
instantiate t u = substTe (singleSub u) t
