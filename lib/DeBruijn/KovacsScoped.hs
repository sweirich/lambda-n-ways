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
import Support.Nat
import qualified Support.Vec as V
import Unsafe.Coerce (unsafeCoerce)
import Util.IdInt
import Util.Impl
import Util.ScopedDeBruijn
import Prelude hiding (length, lookup)

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Kovacs",
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

-- de Bruijn level, type ensures within range
-- offset from the beginning of the context
-- A, B, C |- 0 : A
-- no update required to update the context/range
type Lvl = Idx

-- An environment provides definitions for *indices* and maps them
-- to values in some scope.
data Env l n where
  Nil :: Env l 'Z
  Define :: Env l n -> ~(Val l) -> Env l ('S n)

-- A closure is a term + delayed substitution
data Closure l
  = forall n. Closure (Env l n) (Term ('S n))

data Val l
  = VVar (Lvl l)
  | VApp (Val l) ~(Val l)
  | VLam (Closure l) -- cannot unpack it because of existential

-- NOTE: We can weaken values/environments/closures for free
-- it would be nice if we could do this *safely*
weakenClosure :: Closure l -> Closure ('S l)
weakenClosure = unsafeCoerce

-- Count bindings in the environment
length :: Env l n -> SNat n
length Nil = SZ
length (Define e _) = SS (length e)

-- lookup a value in the environment, based on an *index*
lookupIx :: Ix n -> Env l n -> Val l
lookupIx FZ (Define _env v) = v
lookupIx (FS x) (Define env _) = lookupIx x env

cApp :: Closure l -> Val l -> Val l
cApp (Closure env t) ~u = eval (Define env u) t

eval :: forall l n. Env l n -> Term n -> Val l
eval env = \case
  DVar x -> lookupIx x env
  DApp t u -> case (eval env t, eval env u) of
    (VLam t0, u0) -> cApp t0 u0
    (t0, u0) -> VApp t0 u0
  DLam t -> VLam (Closure env t)

-- Normalization
--------------------------------------------------------------------------------
-- invert the reference to the environment
-- switching between indices and levels
-- i.e.  lvl2Ix x n = n - x - 1
-- unfortunately linear time instead of constant time.

-- go 0 3 = 2
-- go 2 3 = 0
lvl2Ix :: forall n. Lvl n -> SNat n -> Ix n
lvl2Ix FZ (SS n) = sNat2Idx n
lvl2Ix (FS m) (SS n) = FS (lvl2Ix m n)

quote :: forall l. SNat l -> Val l -> Term l
quote l = \case
  VVar x -> DVar (lvl2Ix x l)
  VApp t u -> DApp (quote l t) (quote l u)
  VLam t -> DLam (quote (SS l) (cApp t' (VVar vl)))
    where
      t' :: Closure ('S l)
      t' = weakenClosure t
      vl :: Lvl ('S l)
      vl = sNat2Idx l

nf' :: Env n n -> Term n -> Term n
nf' env t = quote (length env) (eval env t)

nf :: Term 'Z -> Term 'Z
nf t = quote SZ (eval Nil t)