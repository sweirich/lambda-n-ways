module Abstract.DeBruijn where

import Abstract.Class
import qualified Abstract.DeBruijnPar as A
import Abstract.Simple
import Control.Monad.Identity
import Data.Functor.Identity
import Data.List (elemIndex)
import qualified DeBruijn.Par.Subst as S
import Util.Imports

newtype DB = DB Int
  deriving (Eq, Ord, Show, Read, Num, Arbitrary, NFData)

newtype Scope a = Scope a deriving (Eq, NFData)

instance BindingImpl DB where
  type Bnd DB = Scope (LC DB)
  type Subst DB = (,) DB
  type BindM DB = Identity
  runBindM = runIdentity

  aeq x y = return (A.aeqd x y)
  bind v a = return (Scope a)
  unbind (Scope x) = return (DB 0, x)
  toLC = return . A.fromDB
  fromLC = return . A.toDB

  singleton _v a = (DB 0, a)
  subst ss v = return $ uncurry dsubst ss v

instantiate :: LC DB -> LC DB -> LC DB
instantiate b a = dsubst 0 a b

dsubst :: DB -> LC DB -> LC DB -> LC DB
dsubst o s v@(Var i)
  | i == o = adjust 0 s
  | i > o = Var (i -1)
  | otherwise = v
  where
    adjust n e@(Var j)
      | j >= n = Var (j + o)
      | otherwise = e
    adjust n (Lam (Scope e)) = Lam (Scope (adjust (n + 1) e))
    adjust n (App f a) = App (adjust n f) (adjust n a)
dsubst o s (Lam (Scope e)) = Lam (Scope (dsubst (o + 1) s e))
dsubst o s (App f a) = App (dsubst o s f) (dsubst o s a)