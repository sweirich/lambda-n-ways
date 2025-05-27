-- | Simplest use of the unbound-generics library
--   creates Alpha/Subst instances by hand instead of using generic programming
--   uses bind/subst during normalization
module Unbound.UnboundNonGenericsV (impl) where

import qualified Control.DeepSeq as DS
import Control.Monad.Trans (lift)
import GHC.Generics (Generic)
import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Bind as U
import qualified Unbound.Generics.LocallyNameless.Name as U
import Util.IdInt (IdInt (..))
import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC hiding (aeq)

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Unbound.NonUnboundGenericsV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfiTop,
      impl_aeq = U.aeq
    }

type Var = U.Name Exp

data Exp
  = Var !Var
  | Lam !(U.Bind Var Exp)
  | App !Exp !Exp
  deriving (Show, Generic)

instance DS.NFData Exp

instance U.Alpha Exp where
  {-# SPECIALIZE instance U.Alpha Exp #-}
  open c np (Var n) = Var (U.open c np n)
  open c np (Lam bnd) = Lam (U.open c np bnd)
  open c np (App a1 a2) =
    App (U.open c np a1) (U.open c np a2)
  {-# INLINE U.open #-}

  close c np (Var n) = Var (U.close c np n)
  close c np (Lam bnd) = Lam (U.close c np bnd)
  close c np (App a1 a2) =
    App (U.close c np a1) (U.close c np a2)
  {-# INLINE U.close #-}

  aeq' :: U.AlphaCtx -> Exp -> Exp -> Bool
  aeq' c (Var x) (Var y) = U.aeq' c x y
  aeq' c (Lam bnd1) (Lam bnd2) = U.aeq' c bnd1 bnd2
  aeq' c (App a1 a2) (App b1 b2) = U.aeq' c a1 b1 && U.aeq' c a2 b2
  aeq' _ _ _ = False
  {-# INLINE U.aeq' #-}

instance U.Subst Exp Exp where
  {-# SPECIALIZE instance U.Subst Exp Exp #-}

  -- subst :: Name a -> a -> b -> b
  subst :: U.Name Exp -> Exp -> Exp -> Exp
  subst x b a@(Var y) = if x == y then b else a
  subst x b (Lam bnd) = Lam (U.subst x b bnd)
  subst x b (App a1 a2) = App (U.subst x b a1) (U.subst x b a2)

  substBvs :: U.AlphaCtx -> [Exp] -> Exp -> Exp
  substBvs ctx bs (Var x@(U.Bn j k)) 
     | U.ctxLevel ctx == j, fromInteger k < length bs = bs !! fromInteger k
  substBvs ctx bs (Var x) = Var x 
  substBvs ctx bs (Lam bnd) = 
    Lam (U.substBvs ctx bs bnd)
  substBvs ctx bs (App a1 a2) = 
    App (U.substBvs ctx bs a1) (U.substBvs ctx bs a2)
  {-# INLINE U.subst #-}

---------------------------------------------------------------

-- Normalization must be done in a freshness monad.
-- We use the one from unbound-generics
nf :: Exp -> Exp
nf = U.runFreshM . nfd

nfd :: Exp -> U.FreshM Exp
nfd e@(Var _) = return e
nfd (Lam e) =
  do
    (x, e') <- U.unbind e
    e1 <- nfd e'
    return $ Lam (U.bind x e1)
nfd (App f a) = do
  f' <- whnf f
  a' <- whnf a
  case f' of
    Lam b -> do
      nfd (U.instantiate b [a])
      --(x, b') <- U.unbind b
      --nfd (U.subst x a b')
    _ -> App <$> nfd f' <*> nfd a

whnf :: Exp -> U.FreshM Exp
whnf e@(Var _) = return e
whnf e@(Lam _) = return e
whnf (App f a) = do
  f' <- whnf f
  a' <- whnf a
  case f' of
    Lam b -> do
      whnf (U.instantiate b [a'])
      --(x, b') <- U.unbind b
      --whnf (U.subst x a b')
    _ -> return $ App f' a

---------------------------------------------------------------

nfiTop :: Int -> Exp -> Stats.M Exp
nfiTop x e = U.runFreshMT (nfi x e)

nfi :: Int -> Exp -> U.FreshMT Stats.M Exp
nfi 0 _ = lift Stats.done
nfi _ e@(Var _) = return e
nfi n (Lam e) =
  do
    (x, e') <- U.unbind e
    e1 <- nfi (n -1) e'
    return $ Lam (U.bind x e1)
nfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    Lam b -> do
      (x, b') <- U.unbind b
      lift Stats.count
      nfi (n -1) (U.subst x a b')
    _ -> App <$> nfi (n -1) f' <*> nfi (n -1) a

-- Compute the weak head normal form.

whnfi :: Int -> Exp -> U.FreshMT Stats.M Exp
whnfi 0 _ = lift Stats.done
whnfi _ e@(Var _) = return e
whnfi _ e@(Lam _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    Lam b -> do
      lift Stats.count
      (x, b') <- U.unbind b
      whnfi (n -1) (U.subst x a b')
    _ -> return $ App f' a

-- Convert from LC type to DB type (try to do this in linear time??)

toDB :: LC.LC IdInt -> Exp
toDB = to
  where
    to :: LC.LC IdInt -> Exp
    to (LC.Var v) = Var (i2n v)
    to (LC.Lam x b) = Lam (U.bind (i2n x) (to b))
    to (LC.App f a) = App (to f) (to a)

-- Convert back from deBruijn to the LC type.

n2i :: Var -> IdInt
n2i n = IdInt (fromInteger (U.name2Integer n))

i2n :: IdInt -> Var
i2n (IdInt x) = U.s2n (show x)

fromDB :: Exp -> LC.LC IdInt
fromDB = U.runFreshM . from
  where
    from :: Exp -> U.FreshM (LC.LC IdInt)
    from (Var n) = return $ LC.Var (n2i n)
    from (Lam b) = do
      (x, a) <- U.unbind b
      LC.Lam (n2i x) <$> from a
    from (App f a) = LC.App <$> from f <*> from a
