{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

-- Adapted from CPDT

module DeBruijn.Chlipala where

import Control.DeepSeq
import Data.Maybe (fromJust)
import Data.Type.Equality
import IdInt
import Util.Impl
import Util.Lambda
import Util.Nat

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.Chlipala",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

-------------------------------------------------------
-------------------------------------------------------

data DB (n :: Nat) where
  DVar :: !(Idx n) -> DB n
  DApp :: !(DB n) -> !(DB n) -> DB n
  DLam :: !(DB ('S n)) -> DB n

{-
The classic implementation of substitution in de Bruijn terms requires an auxiliary operation, lifting, which increments the indices of all free variables in an expression. We need to lift whenever we "go under a binder." It is useful to write an auxiliary function liftVar that lifts a variable; that is, liftVar x y will return y + 1 if y >= x, and it will return y otherwise. This simple description uses numbers rather than our dependent fin family, so the actual specification is more involved.

Combining a number of dependent types tricks, we wind up with this concrete realization.
-}

liftVar :: Idx n -> Idx (Pred n) -> Idx n
liftVar x y =
  case x of
    FZ -> FS y
    FS x' -> case y of
      FZ -> FZ
      FS y' -> FS (liftVar x' y')

{-

Now it is easy to implement the main lifting operation.
-}

lift :: DB n -> Idx ('S n) -> DB ('S n)
lift e = case e of
  DVar f' -> \f -> DVar (liftVar f f')
  DApp e1 e2 -> \f -> DApp (lift e1 f) (lift e2 f)
  DLam e1 -> \f -> DLam (lift e1 (FS f))

{-
To define substitution itself, we will need to apply some explicit type casts, based on equalities between types. A single equality will suffice for all of our casts. Its statement is somewhat strange: it quantifies over a variable f of type fin n, but then never mentions f. Rather, quantifying over f is useful because fin is a dependent type that is inhabited or not depending on its index. The body of the theorem, S pred( n) = n, is true only for n , but we can prove it by contradiction when n = 0, because we have around a value f of the uninhabited type fin 0.
-}

nzf :: Idx n -> S (Pred n) :~: n
nzf FZ = Refl
nzf (FS _) = Refl

{-
Now we define a notation to streamline our cast expressions. The code f[ return n, r for e] denotes a cast of expression e whose type can be obtained by substituting some number n1 for n in r. f should be a proof that n1 = n2, for any n2. In that case, the type of the cast expression is r with n2 substituted for n.

Notation "[ f 'return' n , r 'for' e ]" :=
  match f in _ = n return r with
    | refl_equal => e
  end.

This notation is useful in defining a variable substitution operation. The idea is that substVar x y returns None if x = y; otherwise, it returns a "squished" version of y with a smaller fin index, reflecting that variable x has been substituted away. Without dependent types, this would be a simple definition. With dependency, it is reasonably intricate, and our main task in automating proofs about it will be hiding that intricacy.
-}

substVar :: Idx n -> Idx n -> Maybe (Idx (Pred n))
substVar x = case x of
  FZ -> \y ->
    case y of
      FZ -> Nothing
      FS f' -> Just f'
  FS x' -> \y ->
    ( case y of
        FZ -> Just $ case (nzf x') of Refl -> FZ -- [nzf x' return n, fin n for FZ]
        FS y' ->
          case substVar x' y' of
            Nothing -> Nothing
            Just f -> Just $ case (nzf y') of Refl -> FS f -- [nzf y' return n, fin n for FS f]
    )

{-

It is now easy to define our final substitution function. The abstraction case involves two casts, where one uses the sym_eq function to convert a proof of n1 = n2 into a proof of n2 = n1.

-}

subst :: DB n -> Idx n -> DB (Pred n) -> DB (Pred n)
subst e f v = case e of
  DVar f' -> case substVar f f' of
    Nothing -> v
    Just f'' -> DVar f''
  DApp e1 e2 -> DApp (subst e1 f v) (subst e2 f v)
  DLam e1 ->
    case (nzf f) of
      Refl -> DLam (subst e1 (FS f) (lift v FZ))

instantiate :: DB (S n) -> DB n -> DB n
instantiate b a = subst b FZ a

-----------------------------------------------------

instance NFData (DB a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b

instance Eq (DB n) where
  DVar x == DVar y = x == y
  DLam x == DLam y = x == y
  DApp x1 x2 == DApp y1 y2 = x1 == y1 && x2 == y2
  _ == _ = False

nfd :: DB n -> DB n
nfd e@(DVar _) = e
nfd (DLam b) = DLam (nfd b)
nfd (DApp f a) =
  case whnf f of
    DLam b -> nfd (instantiate b a)
    f' -> DApp (nfd f') (nfd a)

whnf :: DB n -> DB n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a

nfi :: Int -> DB n -> Maybe (DB n)
nfi 0 e = Nothing
nfi n e@(DVar _) = return e
nfi n (DLam b) = DLam <$> nfi (n -1) b
nfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> nfi (n -1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> DB n -> Maybe (DB n)
whnfi 0 e = Nothing
whnfi n e@(DVar _) = return e
whnfi n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case whnf f' of
    DLam b -> whnfi (n -1) (instantiate b a)
    _ -> return $ DApp f' a

toDB :: LC IdInt -> DB Z
toDB = to []
  where
    to :: [(IdInt, Idx n)] -> LC IdInt -> DB n
    to vs (Var v) = DVar (fromJust (lookup v vs))
    to vs (Lam v b) = DLam (b')
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)

fromDB :: DB n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> DB n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - (toInt i) -1))
    from n (DLam b) = Lam n (from (succ n) b)
    from n (DApp f a) = App (from n f) (from n a)

{-
 > next :: [(Idx n, IdInt)] -> (IdInt, [(Idx (S n), IdInt)])
> next []             = (firstBoundId, [(FZ, firstBoundId)])
> next ((_n, i):rest) = (succ i,        (FZ, succ i): mapFst FS rest)

> mapFst :: (a -> b) -> [(a,c)] -> [(b,c)]
> mapFst f = map (\ (v,i) -> (f v, i))
> -}

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))