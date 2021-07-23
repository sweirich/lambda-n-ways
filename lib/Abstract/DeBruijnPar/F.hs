module Abstract.DeBruijnPar.F where

import Abstract.Class
import qualified Abstract.DeBruijnPar as A
import Abstract.Simple
import Data.Functor.Identity
import Data.List (elemIndex)
import Util.Imports

newtype DB = DB Int
  deriving (Eq, Ord, Show, Read, Num, Arbitrary, NFData)

newtype Sub v = Sub (DB -> v)

newtype DBind v a = DBind (v, a)
  deriving (Eq, Ord, Show, Arbitrary, NFData)

dbind :: v -> a -> DBind v a
dbind x y = DBind (x, y)

dunbind :: DBind v a -> (v, a)
dunbind (DBind b) = b

applySub :: Sub (LC DB) -> DB -> LC DB
{-# INLINE applySub #-}
applySub (Sub f) = f

lift :: Sub (LC DB) -> Sub (LC DB)
{-# INLINE lift #-}
lift s = consSub (Var 0) (s <> incSub 1)

single :: LC DB -> Sub (LC DB)
{-# INLINE single #-}
single t = consSub t idSub

idSub :: Sub (LC DB)
{-# INLINE idSub #-}
idSub = Sub Var

incSub :: DB -> Sub (LC DB)
{-# INLINE incSub #-}
incSub y = Sub (\x -> Var (y + x))

consSub :: LC DB -> Sub (LC DB) -> Sub (LC DB)
{-# INLINE consSub #-}
consSub t ts = Sub $ \x ->
  if x < 0
    then Var x
    else
      if x == 0
        then t
        else applySub ts (x - 1)

instance Semigroup (Sub (LC DB)) where
  s1 <> s2 = Sub $ \x -> substd s2 (applySub s1 x)

instance Monoid (Sub (LC DB)) where
  mempty = idSub

instance BindingImpl DB where
  type Bnd DB = DBind DB (LC DB)
  type Subst DB = Sub
  type BindM DB = Identity
  runBindM = runIdentity

  aeq x y = return $ A.aeqd x y
  bind v a = return $ dbind v a
  unbind = return . dunbind
  toLC = return . A.fromDB
  fromLC = return . A.toDB

  singleton _v a = single a

  subst s a = return (substd s a)

substd :: Sub (LC DB) -> LC DB -> LC DB
substd s (Var x) = applySub s x
substd s (Lam (DBind (v, e))) = Lam (DBind (v, substd (lift s) e))
substd s (App f a) = App (substd s f) (substd s a)