{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Strict #-}

-- Operational aspects of untyped Normalisation by Evaluation
-- KLAUS AEHLIG† and FELIX JOACHIMSKI
-- https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/operational-aspects-of-untyped-normalisation-by-evaluation/18A966EEA5E5760D3DBCCBECF4A9EC0D
-- MSCS 2004

module NBE.Aelig (impl) where

import Data.Maybe (fromJust)
import Util.Impl
import Util.Syntax.DeBruijn
import Util.Syntax.Lambda as LC

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "NBE.Aelig",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "undefiend",
      impl_aeq = (==)
    }

type Lvl = Int

type TERM = Lvl -> DB

inspect :: TERM -> DB
inspect f = f 0
{-# INLINE inspect #-}

freevar :: Int -> TERM
freevar k = \l -> DVar (l + k)

appTERM :: TERM -> TERM -> TERM
appTERM r s = \l -> DApp (r l) (s l)

absTERM :: TERM -> TERM
absTERM r = \l -> DLam (r (l + 1))

boundvar :: Int -> TERM
boundvar k = \l -> DVar (l - k - 1)

data Val
  = Up TERM
  | ABS (Val -> Val)

appVal :: Val -> Val -> Val
appVal (ABS f) ~r = f r
appVal (Up r) ~s = Up (appTERM r (quote s))

quote :: Val -> TERM
quote (Up r) = r
quote (ABS f) = \l -> absTERM (quote (f (Up (boundvar l)))) l

type Env = [Val]

eval :: DB -> Env -> Val
eval (DVar n) rho = rho !! n
eval (DLam r) rho = ABS (\ ~a -> eval r (a : rho))
eval (DApp r s) rho = eval r rho `appVal` eval s rho

xi :: Int -> Val
xi = Up . freevar

nf :: DB -> DB
nf r = inspect (quote (eval r [])) -- [Up (freevar x) | x <- [0 ..]]))