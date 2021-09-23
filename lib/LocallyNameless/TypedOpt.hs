{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS -fno-warn-unticked-promoted-constructors #-}

-- | Based directly on transliteration of Coq output for Ott Locally
-- Nameless Backend
-- Then with types addded, and multi substitutions
-- And caching openning substitutions at binders
-- and caching closing substitutions at binders
-- NOTE: for MANY proofs, this file uses unsafeCoerce
-- That's why this file has been deprecated.
module LocallyNameless.TypedOpt (impl) where

import qualified Control.Monad.State as State
import Data.List (elemIndex)
import Support.TypedSubstOpt
import Util.IdInt
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Impl
import Util.Imports hiding (S, from, to)
import Util.Nat
import qualified Util.Stats as Stats
import qualified Util.Syntax.Lambda as LC

-------------------------------------------------------------------

-- Exp Z is  locally closed terms
data Exp (n :: Nat) where
  Var :: !(Var n) -> Exp n
  Abs :: !(Bind Exp n) -> Exp n
  App :: !(Exp n) -> !(Exp n) -> Exp n
  deriving (Generic, Eq)

deriving instance Show (Exp n)

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "LocallyNameless.TypedOpt",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = undefined,
      impl_aeq = (==)
    }

instance VarC Exp where
  var = Var

  isvar (Var x) = Just x
  isvar _ = Nothing

instance AlphaC Exp where
  fv :: Exp n -> S.IdIntSet
  fv e =
    case e of
      (Var (B _)) -> S.empty
      (Var (F x)) -> S.singleton x
      (Abs b) -> fv (unbind b)
      (App e1 e2) -> fv e1 `S.union` fv e2

  multi_open_rec ss (Var x) = Var (multi_open_rec ss x)
  multi_open_rec ss (App a b) = App (multi_open_rec ss a) (multi_open_rec ss b)
  multi_open_rec ss (Abs b) = Abs (multi_open_rec ss b)

  multi_close_rec k ss (Var x) = Var (multi_close_rec k ss x)
  multi_close_rec k ss (App a b) = App (multi_close_rec k ss a) (multi_close_rec k ss b)
  multi_close_rec k ss (Abs b) = Abs (multi_close_rec k ss b)

instance SubstC (Exp 'Z) Exp where
  multi_subst_fv ss (Var x) = multiSubstFvVar ss x
  multi_subst_fv ss (App a b) = App (multi_subst_fv ss a) (multi_subst_fv ss b)
  multi_subst_fv ss (Abs b) = Abs (multi_subst_fv ss b)

  multi_subst_bv ss (Var x) = multiSubstBvVar ss x
  multi_subst_bv ss (App a b) = App (multi_subst_bv ss a) (multi_subst_bv ss b)
  multi_subst_bv ss (Abs b) = Abs (multi_subst_bv ss b)

{- ------------------------------------------ -}

toDB :: LC.LC IdInt -> Exp Z
toDB = to SZ []
  where
    to :: SNat n -> [(IdInt, Idx n)] -> LC.LC IdInt -> Exp n
    to _ vs (LC.Var v) = maybe (Var (F v)) (Var . B) (lookup v vs)
    to k vs (LC.Lam x b) = Abs (bind b')
      where
        b' = to (SS k) ((x, FZ) : mapSnd FS vs) b
    to k vs (LC.App f a) = App (to k vs f) (to k vs a)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

fromDB :: Exp n -> LC.LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Exp n -> LC.LC IdInt
    from _ (Var (F v)) = LC.Var v
    from (IdInt n) (Var (B i))
      | toInt i < 0 = LC.Var (IdInt $ toInt i)
      | toInt i >= n = LC.Var (IdInt $ toInt i)
      | otherwise = LC.Var (IdInt (n - (toInt i) -1))
    from n (Abs b) = LC.Lam n (from (succ n) (unbind b))
    from n (App f a) = LC.App (from n f) (from n a)

instance NFData (Exp n) where
  rnf (Var i) = rnf i
  rnf (Abs b) = rnf b
  rnf (App a b) = rnf a `seq` rnf b

{- --------------------------------------- -}

type N a = State IdInt a

newVar :: (MonadState IdInt m) => m IdInt
newVar = do
  i <- get
  put (succ i)
  return i

nfd :: Exp Z -> Exp Z
nfd e = State.evalState (nf' e) firstBoundId

nf' :: Exp Z -> N (Exp Z)
nf' e@(Var (F _)) = return e
--nf' e@(Var_b _) = error "should not reach this"
nf' (Abs b) = do
  x <- newVar
  b' <- nf' (open b x)
  return $ Abs (close x b')
nf' (App f a) = do
  f' <- whnf f
  case f' of
    Abs b ->
      nf' (instantiate b a)
    _ -> App <$> nf' f' <*> nf' a

-- Compute the weak head normal form.
whnf :: Exp Z -> N (Exp Z)
whnf e@(Var (F _)) = return e
--whnf e@(Var_b _) = error "BUG"
whnf e@(Abs _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    (Abs b) -> whnf (instantiate b a)
    _ -> return $ App f' a

-- Fueled version

{-
nfi :: Int -> Exp Z -> Maybe (Exp Z)
nfi n e = State.evalStateT (nfi' n e) firstBoundId

type NM a = State.StateT IdInt Stats.M a

nfi' :: Int -> (Exp Z) -> NM (Exp Z)
nfi' 0 _ = State.lift Stats.done
nfi' _n e@(Var_f _) = return e
--nfi' n e@(Var_b _) = error "should not reach this"
nfi' n (Abs e) = do
  x <- newVar
  e' <- nfi' (n - 1) (open e (Var_f x))
  return $ Abs (close x e')
nfi' n (App f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    Abs b -> State.lift Stats.count >> nfi' (n - 1) (open b a)
    _ -> App <$> nfi' (n - 1) f' <*> nfi' (n -1) a

-- Compute the weak head normal form.
whnfi :: Int -> Exp Z -> NM (Exp Z)
whnfi 0 _ = State.lift Stats.done
whnfi _n e@(Var_f _) = return e
--whnfi n e@(Var_b _) = error "BUG"
whnfi _n e@(Abs _) = return e
whnfi n (App f a) = do
  f' <- whnfi (n -1) f
  case f' of
    (Abs b) -> State.lift Stats.count >> whnfi (n -1) (open b a)
    _ -> return $ App f' a
    -}