{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

-- https://github.com/AndrasKovacs/elaboration-zoo/blob/master/01-eval-closures-debruijn/Main.hs

-- This implementation relies on the laziness of Haskell to implement call-by-need normal order evaluation.

-- SCW added well-scoped expressions to keep track of DeBruijn indices
-- and levels.

-- If the ~ were removed below, then this implementation would be for a different evaluation order.
-- As it is, because of Haskell's laziness, it doesn't do nearly as much work as the other versions.

module NBE.KovacsScoped where

import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)
import Util.IdInt
import Util.Impl
import Util.Nat
import Util.Syntax.ScopedDeBruijn
import qualified Util.Vec as V
import Prelude hiding (length, lookup)

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "NBE.KovacsScoped",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "undefiend",
      impl_aeq = (==),
      impl_eval = nf
    }

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

-- | Representation of terms using de bruijn levels
-- and closures (i.e. delayed substitutions) for
-- abstractions
-- This could be related to locally nameless
-- representation, which works with "locally closed" terms
-- only.
data Val
  = VVar {-# UNPACK #-} Lvl
  | -- | Original version had lazy argument, but that is not needed
    VApp Val Val
  | -- | existential in closure prevents unpacking, so we
    -- do it manually here
    -- Lambdas are "locally closed" all external bound variables
    -- in the term must have been substituted with values
    forall n. VLam (Env n) (Term ('S n))
  | VBool {-# UNPACK #-} Bool
  | forall n. VIf Val (Env n) (Term n) (Term n)

-- | Count bindings in the environment
-- recovers the runtime value from the compiletime only version
-- original version was tail recursive. But that is more difficult
-- to type check.
length :: Env n -> SNat n
length Nil = SZ
length (Define e _) = SS (length e)

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
  DApp t u -> case (eval env t) of
    (VLam e0 t0) -> eval (Define e0 (eval env u)) t0
    t0 -> VApp t0 (eval env u)
  DLam t -> VLam env t
  DBool b -> VBool b
  DIf t u v -> case (eval env t) of
    VBool True -> eval env u
    VBool False -> eval env v
    t0 -> VIf t0 env u v

-- | Convert a value to to a term by translating
-- all level-based vars to index-based vars
quote :: forall l. SNat l -> Val -> Term l
quote l = \case
  VVar x -> DVar (lvl2Ix x l)
  VApp t u -> DApp (quote l t) (quote l u)
  VLam t e -> DLam (quote (SS l) (cApp t e (VVar vl)))
    where
      vl :: Lvl
      vl = sNat2Int l
  VBool b -> DBool b
  VIf t env u v -> 
    DIf (quote l t) (quote l (eval env u)) (quote l (eval env v))

-- Normalization
--------------------------------------------------------------------------------

-- | invert the reference to the environment
-- switching between indices and levels
-- i.e.  lvl2Ix x n = n - x - 1
-- unfortunately linear time instead of constant time.
-- but adds minimal overhead.
lvl2Ix :: forall n. Int -> SNat n -> Ix n
lvl2Ix x l = toIdx l (sNat2Int l - x - 1)

nf' :: Env n -> Term n -> Term n
nf' env t = quote (length env) (eval env t)

nf :: Term 'Z -> Term 'Z
nf t = quote SZ (eval Nil t)