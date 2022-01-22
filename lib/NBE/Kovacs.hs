{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

-- https://github.com/AndrasKovacs/elaboration-zoo/blob/master/01-eval-closures-debruijn/Main.hs

-- This implementation relies on the laziness of Haskell to implement call-by-need normal order evaluation.
-- If the ~ were removed below, then this implementation would be for a different evaluation order.

module NBE.Kovacs where

import Util.IdInt
import Util.Impl
import Util.Syntax.DeBruijn
import Prelude hiding (length, lookup)

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "NBE.Kovacs",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "undefiend",
      impl_aeq = (==)
    }

type Ix = Int

type Lvl = IdInt

data Env
  = Nil
  | Define Env ~Val

data Closure
  = Closure Env DB

data Val
  = VVar {-# UNPACK #-} Lvl
  | VApp Val Val
  | VLam {-# UNPACK #-} Closure

length :: Env -> Lvl
length = go 0
  where
    go acc Nil = acc
    go acc (Define env _) = go (acc + 1) env

-- Normalization
--------------------------------------------------------------------------------

lookup :: Env -> Ix -> Val
lookup (Define _env v) 0 = v
lookup (Define env _) x = lookup env (x - 1)
lookup _ _ = error "index out of scope"

appVal :: Val -> Val -> Val
appVal (VLam (Closure env t)) ~u = eval (Define env u) t
appVal t0 ~u = VApp t0 u

eval :: Env -> DB -> Val
eval env = \case
  DVar x -> lookup env x
  DApp t u -> appVal (eval env t) (eval env u)
  DLam t -> VLam (Closure env t)

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (IdInt l) (IdInt x) = (l - x - 1)

type TERM = Lvl -> DB

appTERM :: TERM -> TERM -> TERM
appTERM r s = \l -> DApp (r l) (s l)

absTERM :: TERM -> TERM
absTERM r = \l -> DLam (r (l + 1))

varTERM :: IdInt -> TERM
varTERM k = \l -> DVar (lvl2Ix l k)

quote :: Val -> TERM
quote = \case
  VVar x -> varTERM x
  VApp t u -> appTERM (quote t) (quote u)
  v@(VLam _) -> \l -> absTERM (quote (appVal v (VVar l))) l

-- \l -> DLam (quote (appVal v (VVar l)) (l + 1))

nf' :: Env -> DB -> DB
nf' env t = quote (eval env t) (length env)

nf :: DB -> DB
nf t = quote (eval Nil t) 0