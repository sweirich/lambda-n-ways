{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

-- https://github.com/AndrasKovacs/elaboration-zoo/blob/master/01-eval-closures-debruijn/Main.hs

-- This implementation relies on the laziness of Haskell to implement call-by-need normal order evaluation.

-- It also uses well-scoped expressions to keep track of DeBruijn indices
-- and levels.

-- If the ~ were removed below, then this implementation would be for a different evaluation order.
-- As it is, because of Haskell's laziness, it doesn't do nearly as much work as the other versions.

module DeBruijn.KovacsScoped where

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
    { impl_name = "DeBruijn.KovacsScoped",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "undefiend",
      impl_aeq = (==)
    }

-- de Bruijn index, type ensures within range
-- offset from the end of the context
--  A, B, C |- 0 : C
-- value must be updated (shifted) if context/range is weakened/strengthened
type Ix = Idx

-- de Bruijn level
-- offset from the beginning of the context
-- A, B, C |- 0 : A
-- no update required to update the context/range
type Lvl = Int

-- An environment provides definitions for *indices* and maps them
-- to values.
data Env n where
  Nil :: Env 'Z
  Define :: Env n -> ~Val -> Env ('S n)

-- A closure is a term + delayed substitution
data Closure
  = forall n. Closure (Env n) (Term ('S n))

data Val
  = VVar Lvl
  | VApp Val ~Val
  | -- | existential in closure prevents this auto-unpacking
    forall n. VLam (Env n) (Term ('S n))

-- Count bindings in the environment
length :: Env n -> SNat n
length Nil = SZ
length (Define e _) = SS (length e)

-- lookup a value in the environment, based on an *index*
lookupIx :: Ix n -> Env n -> Val
lookupIx FZ (Define _env v) = v
lookupIx (FS x) (Define env _) = lookupIx x env

cApp :: (Env n) -> (Term ('S n)) -> Val -> Val
cApp env t ~u = eval (Define env u) t

eval :: forall n. Env n -> Term n -> Val
eval env = \case
  DVar x -> lookupIx x env
  DApp t u -> case (eval env t, eval env u) of
    (VLam t0 e0, u0) -> cApp t0 e0 u0
    (t0, u0) -> VApp t0 u0
  DLam t -> VLam env t

-- Normalization
--------------------------------------------------------------------------------
-- invert the reference to the environment
-- switching between indices and levels
-- i.e.  lvl2Ix x n = n - x - 1
-- unfortunately linear time instead of constant time.
-- but adds minimal overhead.
lvl2Ix :: forall n. Int -> SNat n -> Ix n
lvl2Ix x l = toIdx l (sNat2Int l - x - 1)

toIdx :: SNat n -> Int -> Ix n
toIdx (SS _n) 0 = FZ
toIdx (SS n) m | m > 0 = FS (toIdx n (m -1))
toIdx _ m = error "error"

quote :: forall l. SNat l -> Val -> Term l
quote l = \case
  VVar x -> DVar (lvl2Ix x l)
  VApp t u -> DApp (quote l t) (quote l u)
  VLam t e -> DLam (quote (SS l) (cApp t e (VVar vl)))
    where
      vl :: Lvl
      vl = sNat2Int l

nf' :: Env n -> Term n -> Term n
nf' env t = quote (length env) (eval env t)

nf :: Term 'Z -> Term 'Z
nf t = quote SZ (eval Nil t)