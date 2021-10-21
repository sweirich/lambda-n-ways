{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE ViewPatterns #-}

-- adapted from
-- https://github.com/AndrasKovacs/elaboration-zoo/blob/master/01-eval-closures-names/Main.hs

module NBE.KovacsNamed where

import Data.Maybe (fromJust)
import Util.IdInt
import Util.Impl
import Util.Syntax.Lambda

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "NBE.KovacsNamed",
      impl_fromLC = id,
      impl_toLC = id,
      impl_nf = nf [],
      impl_nfi = error "unimplemented",
      impl_aeq = aeq
    }

type Name = IdInt

type Tm = LC Name

type Env = [(Name, Val)]

data Val
  = VVar Name
  | VApp Val Val
  | VLam {-# UNPACK #-} Closure

data Closure = Cl Name Env Tm

-- we can do better than this
fresh :: [Name] -> Name -> Name
fresh [] x = x
fresh ns x = case elem x ns of
  True -> fresh ns (x + 1)
  False -> x

appCl :: Closure -> Val -> Val
appCl (Cl x env t) ~u = eval ((x, u) : env) t

freshCl :: [Name] -> Closure -> (Name, Closure)
freshCl ns cl@(Cl x _ _) = (fresh ns x, cl)

eval :: Env -> Tm -> Val
eval env = \case
  Var x -> fromJust $ lookup x env
  App t u -> case (eval env t, eval env u) of
    (VLam cl, u0) -> appCl cl u0
    (t0, u0) -> VApp t0 u0
  Lam x t -> VLam (Cl x env t)

quote :: [Name] -> Val -> Tm
quote ns = \case
  VVar x -> Var x
  VApp t u -> App (quote ns t) (quote ns u)
  VLam (freshCl ns -> (x, cl)) -> Lam x (quote (x : ns) (appCl cl (VVar x)))

nf :: Env -> Tm -> Tm
nf env = quote (map fst env) . eval env