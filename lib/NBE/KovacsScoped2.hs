{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

-- https://github.com/AndrasKovacs/elaboration-zoo/blob/master/01-eval-closures-debruijn/Main.hs

-- This implementation relies on the laziness of Haskell to implement call-by-need normal order evaluation.

-- It also uses well-scoped expressions to keep track of DeBruijn indices
-- and levels.

-- It also combines the Term and Val datatypes togther into a single data type
-- in order to compare with locally nameless representation.

-- If the ~ were removed below, then this implementation would be for a different evaluation order.
-- As it is, because of Haskell's laziness, it doesn't do nearly as much work as the other versions.

module NBE.KovacsScoped2 where

import Control.DeepSeq
import Data.Kind (Type)
import Data.Maybe (fromJust)
import Data.Type.Equality
import Debug.Trace
import Unsafe.Coerce (unsafeCoerce)
import Util.IdInt
import Util.Impl
import Util.Nat
import Util.Syntax.Lambda as LC
import qualified Util.Vec as V
import Prelude hiding (length)
import Debug.Trace

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "NBE.KovacsScoped2",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "undefiend",
      impl_aeq = (==)
    }

data Term :: Nat -> Type where
  DVar :: Idx g -> Term g
  DLvl :: Lvl -> Term g
  DLam :: Term ('S g) -> Term g
  DClo :: Closure -> Term 'Z
  DApp :: Term g -> Term g -> Term g

instance NFData (Term a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DClo c) = rnf c
  rnf (DLvl l) = rnf l

instance NFData Closure where
  rnf (Closure e t) = rnf e `seq` rnf t

instance NFData (Env a) where
  rnf Nil = ()
  rnf (Define e v) = rnf e `seq` rnf v

deriving instance Eq (Term n)

deriving instance Eq (Env n)

-- | de Bruijn index, type ensures within scope
-- used in terms
-- offset from the end of the context/environment
--  A, B, C |- 0 : C
-- terms must be updated (shifted) if context/scope is weakened/strengthened
type Ix = Idx

-- | de Bruijn level, used in values
-- offset from the beginning of the context/environment
-- A, B, C |- 0 : A
-- values never need to be shifted
type Lvl = Int

-- | An environment provides definitions for *indices* and maps them
-- to values. Values only refer to levels.
-- n is the number of definitions in the environment
data Env (n :: Nat) where
  Nil :: Env 'Z
  -- | Lazy RHS is essential for cbn evaluation
  Define :: Env n -> ~Val -> Env ('S n)

-- | A closure is a term + delayed substitution
-- We don't actually use this definition
data Closure
  = forall n. Closure (Env n) (Term ('S n))

instance Eq Closure where
  (Closure e1 t1) == (Closure e2 t2) =
    case testEquality (length e1) (length e2) of
      Just Refl -> e1 == e2 && t1 == t2
      Nothing -> False

-- | Representation of terms using de bruijn levels
-- and closures (i.e. delayed substitutions) for
-- abstractions
-- This could be related to locally nameless
-- representation, which works with "locally closed" terms
-- only.
type Val = Term 'Z

-- | Count bindings in the environment
-- recovers the runtime value from the compiletime only version
-- original version was tail recursive. But that is more difficult
-- to type check.
length :: Env n -> SNat n
length Nil = SZ
length (Define e _) = SS (length e)

{-
length' :: Env n -> SNat n
length' = go SZ
  where
    go :: SNat m -> Env (Plus m n) -> SNat n
    go acc Nil = acc
    go acc (Define env _) = go (SS acc) env
-}

-- | lookup a value in the environment, based on an *index*
lookupIx :: Ix n -> Env n -> Val
lookupIx FZ (Define _env v) = v
lookupIx (FS x) (Define env _) = lookupIx x env

-- | Apply a closure (i.e. env + term) to a value
cApp :: (Env n) -> (Term ('S n)) -> Val -> Val
cApp env t ~u = eval (Define env u) t

eval :: forall n. Env n -> Term n -> Val
eval env = \case
  DVar x -> lookupIx x env
  DLvl y -> DLvl y
  DApp t u -> case (eval env t) of
    (DClo (Closure e0 t0)) ->
      eval (Define e0 (eval env u)) t0
    t0 -> DApp t0 (eval env u)
  DLam t ->
    -- biggest difference: stop here and don't
    -- normalize body of lambda until it is
    -- applied
    DClo (Closure env t)
  DClo c ->
    -- this is an impossible case
    trace "impossible: eval clo" $
      DClo c

-- | Convert a value to to a term by translating
-- all level-based vars to index-based vars
-- This is an analogue to "close" in LN versions
-- The level "l" tells us how to translate DLvl variables
-- to indices
quote :: forall l. SNat l -> Val -> Term l
quote l = \case
  -- DVar x -> know the arg is closed. Can't happen
  DLvl x -> DVar (lvl2Ix x l)
  DApp t u -> DApp (quote l t) (quote l u)
  DLam t ->
    -- this is an impossible case
    trace "impossible: quote lam" $
      DLam (quote (SS l) (cApp Nil t (DLvl vl)))
  DClo (Closure e t) ->
    -- we call eval here. Why? NBE stuff going on
    DLam (quote (SS l) (eval (Define e (DLvl vl)) t))
  where
    vl :: Lvl
    vl = sNat2Int l

eval_quote :: forall n. Env n -> SNat n -> Term n -> Term n
eval_quote env l = \case
  DVar x ->
    -- get closed term from environment. Why can't we quote when
    -- we put it in? We don't know how many "free" vars to re-introduce
    -- (i.e. this is a "shift")
    -- Why don't we wait to eval it when we take it out? Then
    -- we aren't saving the work between multiple copies of the
    -- term
    quote l (lookupIx x env)
  DLvl y -> DVar (lvl2Ix y l)
  DApp t u -> case (eval env t) of
    (DClo (Closure e0 t0)) ->
      quote l (eval (Define e0 (eval env u)) t0)
    _t0 -> DApp (eval_quote env l t) (eval_quote env l u)
  DClo (Closure e t) ->
    trace "eval_quote closure" $
      DLam (quote (SS l) (eval (Define e (DLvl (sNat2Int l))) t))
  DLam t ->
    DLam (eval_quote (Define env (DLvl (sNat2Int l))) (SS l) t)

nf :: Term 'Z -> Term 'Z
nf = eval_quote Nil SZ

nf' :: Env n -> SNat n -> Term n -> Term n
nf' env l t = quote l (eval env t)

-- Normalization
--------------------------------------------------------------------------------

-- | invert the reference to the environment
-- switching between indices and levels
-- i.e.  lvl2Ix x n = n - x - 1
-- unfortunately linear time instead of constant time.
-- but adds minimal overhead.
lvl2Ix :: forall n. Int -> SNat n -> Ix n
lvl2Ix x l = toIdx l (sNat2Int l - x - 1)

--nf' :: Env n -> Term n -> Term n
--nf' env t = quote (length env) (eval env t)

--nf :: Term 'Z -> Term 'Z
-- nf t = quote SZ (eval Nil t)

toDB :: LC IdInt -> Term 'Z
toDB = to []
  where
    to :: [(IdInt, Idx n)] -> LC IdInt -> Term n
    to vs (Var v) = DVar (fromJust (lookup v vs))
    to vs (Lam v b) = DLam b'
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)
    to vs lc = error ("No case for: " ++ show lc) 

-- Convert back from deBruijn to the LC type.

fromDB :: Term n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Term n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - (toInt i) -1))
    from n (DLam b) = Lam n (from (succ n) b)
    from n (DApp f a) = App (from n f) (from n a)
    from n (DLvl x) = Var (IdInt x)
    from n@(IdInt i) (DClo (Closure e t)) =
      Lam n (from (succ n) (cApp e t (DLvl (succ i))))

-- from n (DClo e t) = Lam n (from (succ n) (eval e t))

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))