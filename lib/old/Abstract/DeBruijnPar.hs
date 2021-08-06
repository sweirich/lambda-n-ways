module Abstract.DeBruijnPar where

import Abstract.Class
import Abstract.Simple
import Data.Coerce
import Data.List (elemIndex)
import Util.IdInt
import Util.Imports

-- Generic conversion function for de Bruijn indices
toDB :: forall v. (BindingImpl v, Coercible v Int) => LC IdInt -> LC v
toDB = to []
  where
    toV :: Int -> v
    toV = coerce
    to :: [IdInt] -> LC IdInt -> LC v
    to vs (Var v@(IdInt i)) = maybe (Var (toV i)) (Var . toV) (elemIndex v vs)
    to vs (Lam bnd) = lam' (coerce x) (to (x : vs) b)
      where
        (x, b) = unbind' bnd
    to vs (App f a) = App (to vs f) (to vs a)

--Convert back from deBruijn to the LC type.
fromDB :: forall v. (Coercible v Int, BindingImpl v) => LC v -> LC IdInt
fromDB = from firstBoundId
  where
    toInt :: v -> Int
    toInt = coerce
    from :: IdInt -> LC v -> LC IdInt
    from (IdInt n) (Var i)
      | toInt i < 0 = Var (IdInt (coerce i))
      | toInt i >= coerce n = Var (IdInt (coerce i))
      | otherwise = Var (IdInt (n - coerce i -1))
    from n (Lam bnd) = Lam (bind' n (from (succ n) b))
      where
        (_, b) = unbind' bnd
    from n (App f a) = App (from n f) (from n a)

aeqd :: forall v. (BindingImpl v, Coercible v Int) => LC v -> LC v -> Bool
aeqd (Var x) (Var y) = toInt x == toInt y
  where
    toInt :: v -> Int
    toInt = coerce
aeqd (Lam b1) (Lam b2) = aeqd (snd (unbind' @v b1)) (snd (unbind' @v b2))
aeqd (App a1 a2) (App b1 b2) = aeqd a1 b1 && aeqd a2 b2

{-
substd :: (BindingImpl v, Bnd v ~ DBind v) => Subst v (LC v) -> LC v -> LC v
substd s (Var x) = applySub s x
substd s (Lam (DBind (v, e))) = Lam (DBind (v, substd (lift s) e))
substd s (App f a) = App (substd s f) (substd s a)
-}