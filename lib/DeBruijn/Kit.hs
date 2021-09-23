{-# LANGUAGE DataKinds #-}
{-# OPTIONS  -Wall -fno-warn-unticked-promoted-constructors  #-}
{-# LANGUAGE RecordWildCards #-}

{-
This implementation is derived from Allais et al. below but modified to
represent the untyped lambda calculus. It is similar to the DeBruijn.Par.F
implementation and probably could be optimized in a similar way. The focus of
the original paper is on proofs, so it is not clear that this is an
appropriate implementation for execution.

Another key difference is that

Type-and-Scope Safe Programs and Their Proofs
Guillaume Allais, James Chapman, Conor McBride, James McKinna
-}

module DeBruijn.Kit (impl, prettyPrint) where

import Util.Impl
import Util.Imports
import Util.Nat
import qualified Util.Stats as Stats
import Util.Syntax.ScopedDeBruijn

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Kit",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

type Con = Nat

type SCon = SNat

-- An (evaluation) environment is a collection of environment
-- values covering a given context `g`.

type Environment (d :: Con) (e :: Con -> Type) (g :: Con) =
  Idx g -> e d

envNull :: Environment d e 'Z
envNull v = case v of

envCons :: Environment d e g -> e d -> Environment d e ('S g)
envCons _ e FZ = e
envCons env _ (FS v) = env v

type Included g d = Environment d Idx g

refl :: forall g. Included g g
refl = id

top :: forall d g. Included g d -> Included g ('S d)
top inc = FS . inc

data Semantics (e :: Con -> Type) (m :: Con -> Type) = Semantics
  { weak :: forall g d. Included g d -> e g -> e d,
    embed :: forall g. Idx g -> e g,
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
    go (DVar v) env = var $ env v
    go (DLam t) env = lam $ \inc v -> go t (envCons (wkEnv sem inc env) v)
    go (DApp f t) env = app (go f env) (go t env)

evalTerm :: forall e m g. Semantics e m -> SCon g -> Term g -> m g
evalTerm sem@Semantics {..} g t = semanticsTerm sem t (env g)
  where
    env :: forall g'. SCon g' -> Environment g' e g'
    env SZ = envNull
    env (SS sg) = envCons (wkEnv sem (top refl) $ env sg) (embed FZ)

------------------------------------------------------------------------
-- Syntactic Semantics
------------------------------------------------------------------------

renaming :: Semantics Idx Term
renaming =
  Semantics
    { weak = \inc v -> inc v,
      embed = id,
      var = DVar,
      app = DApp,
      lam = \t -> DLam $ t (top refl) FZ
    }

weakTe :: Included g d -> Term g -> Term d
weakTe inc t = semanticsTerm renaming t inc

type Subst g d = Environment d Term g

substitution :: Semantics Term Term
substitution =
  Semantics
    { weak = weakTe,
      embed = DVar,
      var = id,
      app = DApp,
      lam = \t -> DLam $ t (top refl) (DVar FZ)
    }

substTe :: Subst g d -> Term g -> Term d
substTe sub t = semanticsTerm substitution t sub

singleSub :: Term g -> Subst ('S g) g
singleSub a FZ = a
singleSub _a (FS m) = DVar m

------------------------------------------------------------------------
-- Pretty Printing Semantics
------------------------------------------------------------------------

newtype Constant k (g :: Con) = Constant {runConstant :: k}

prettyPrinting :: Semantics (Constant String) (Constant (State [String] String))
prettyPrinting =
  Semantics
    { weak = \_ -> Constant . runConstant,
      embed = Constant . show . toInt,
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

prettyPrint :: forall g. SCon g -> Term g -> String
prettyPrint g t = evalState (runConstant $ evalTerm prettyPrinting g t) names
  where
    names = fmap (: []) alpha ++ alphaInt
    alpha = ['a' .. 'z']
    alphaInt = concatMap (\i -> fmap (: show i) alpha) [(0 :: Integer) ..]

------------------------------------------------------------------------
-- Benchmark normalization function (SCW)
------------------------------------------------------------------------

nfd :: Term n -> Term n
nfd e@(DVar _) = e
nfd (DLam b) = DLam (nfd b)
nfd (DApp f a) =
  case whnf f of
    DLam b -> nfd (instantiate b a)
    f' -> DApp (nfd f') (nfd a)

whnf :: Term n -> Term n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a

instantiate :: Term ('S n) -> Term n -> Term n
instantiate t u = substTe (singleSub u) t

nfi :: Int -> Term a -> Stats.M (Term a)
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam <$> nfi (n -1) b
nfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> Term a -> Stats.M (Term a)
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ DApp f' a
