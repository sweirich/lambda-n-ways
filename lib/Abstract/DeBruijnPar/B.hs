module Abstract.DeBruijnPar.B where

import Abstract.Class
import qualified Abstract.DeBruijnPar as A
import Abstract.Simple
import Data.Functor.Identity
import Data.List (elemIndex)
import qualified DeBruijn.Par.Subst as S
import Util.Imports

type Sub = S.Sub

instance S.SubstC (LC DB) where
  var = Var . DB

  subst s x = go s x
    where
      go _s (Var i) = S.applySub s (coerce i)
      go _s (Lam b) = Lam (S.substBind s b)
      go _s (App f a) = App (go s f) (go s a)

newtype DB = DB Int
  deriving (Eq, Ord, Show, Read, Num, Arbitrary, NFData)

instance BindingImpl DB where
  type Bnd DB = S.Bind (LC DB)
  type Subst DB = Sub
  type BindM DB = Identity
  runBindM = runIdentity

  aeq x y = return (A.aeqd x y)
  bind v a = return (S.bind a)
  unbind x = return (DB 0, S.unbind x)
  toLC = return . A.fromDB
  fromLC = return . A.toDB

  singleton _v a = S.single a
  subst ss a = return (S.subst ss a)