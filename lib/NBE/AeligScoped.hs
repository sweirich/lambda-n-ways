{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

-- Operational aspects of untyped Normalisation by Evaluation
-- KLAUS AEHLIG† and FELIX JOACHIMSKI
-- https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/operational-aspects-of-untyped-normalisation-by-evaluation/18A966EEA5E5760D3DBCCBECF4A9EC0D
-- MSCS 2004

module NBE.AeligScoped (impl) where

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
import Util.Syntax.ScopedDeBruijn
import qualified Util.Vec as V
import Prelude hiding (length)

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.AeligScioed",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "undefiend",
      impl_aeq = (==)
    }

type TERM m = forall n. SNat n -> Term (Plus m n)

inspect :: forall m. TERM m -> Term m
inspect f | Just Refl <- = f SZ
{-# INLINE inspect #-}

freevar :: SNat m -> TERM m
freevar k = \n -> DVar (n + k)

appTERM :: TERM m -> TERM m -> TERM m
appTERM r s = \n -> DApp (r n) (s n)

absTERM :: TERM (S m) -> TERM m
absTERM r = \n -> DLam (r (SS n))

boundvar :: Int -> TERM m
boundvar k = \n -> DVar (n - k - 1)

data Val m
  = Up (TERM m)
  | ABS (Val m -> Val m)

appVal :: Val m -> Val m -> Val m
appVal (ABS f) ~r = f r
appVal (Up r) ~s = Up (appTERM r (down s))

down :: Val m -> TERM m
down (Up r) = r
down (ABS f) = \n -> absTERM (down (f (Up (boundvar n)))) n

-- NOTE: using a Int -> Val function is a lot slower

data Env m (n :: Nat) where
  Nil :: Env m 'Z
  -- | Lazy RHS is essential for cbn evaluation
  Define :: Env m n -> ~(Val m) -> Env m ('S n)

-- | lookup a value in the environment, based on an *index*
lookupIx :: Idx n -> Env m n -> Val m
lookupIx FZ (Define _env v) = v
lookupIx (FS x) (Define env _) = lookupIx x env

eval :: Term n -> Env m n -> Val m
eval (DVar n) rho = lookupIx n rho
eval (DLam r) rho = ABS (\ ~a -> eval r (Define rho a))
eval (DApp r s) rho = eval r rho `appVal` eval s rho

nf :: Term Z -> Term Z
nf r = inspect (down (eval r Nil)) -- [Up (freevar x) | x <- [0 ..]]))