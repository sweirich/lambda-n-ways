{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

-- https://github.com/AndrasKovacs/elaboration-zoo/blob/master/01-eval-closures-debruijn/Main.hs

-- This implementation relies on the laziness of Haskell to implement call-by-need normal order evaluation.
-- If the ~ were removed below, then this implementation would be for a different evaluation order.
-- As it is, because of Haskell's laziness, it doesn't do nearly as much work as the other versions.

-- Q1: Can we add laziness to the other nf functions in a nice way?
module DeBruijn.Kovacs where

import Util.DeBruijn
import Util.IdInt
import Util.Impl
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

type Ix = Int

type Lvl = IdInt

data Env
  = Nil
  | Define Env ~Val

data Closure
  = Closure Env DB

data Val
  = VVar Lvl
  | VApp Val ~Val
  | VLam {-# UNPACK #-} Closure

length :: Env -> Lvl
length = go 0
  where
    go acc Nil = acc
    go acc (Define env _) = go (acc + 1) env

lookup :: Env -> Ix -> Val
lookup (Define _env v) 0 = v
lookup (Define env _) x = lookup env (x - 1)
lookup _ _ = error "index out of scope"

cApp :: Closure -> Val -> Val
cApp (Closure env t) ~u = eval (Define env u) t

eval :: Env -> DB -> Val
eval env = \case
  DVar x -> lookup env x
  DApp t u -> case (eval env t, eval env u) of
    (VLam t0, u0) -> cApp t0 u0
    (t0, u0) -> VApp t0 u0
  DLam t -> VLam (Closure env t)

-- Normalization
--------------------------------------------------------------------------------

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (IdInt l) (IdInt x) = (l - x - 1)

quote :: Lvl -> Val -> DB
quote l = \case
  VVar x -> DVar (lvl2Ix l x)
  VApp t u -> DApp (quote l t) (quote l u)
  VLam t -> DLam (quote (l + 1) (cApp t (VVar l)))

nf' :: Env -> DB -> DB
nf' env t = quote (length env) (eval env t)

nf :: DB -> DB
nf t = quote 0 (eval Nil t)