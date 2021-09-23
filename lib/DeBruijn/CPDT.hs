-- | Adapted from CPDT by Adam Chlipala
--
-- This version is intended to demonstrate dependently-typed programming for well-scoped
-- de Bruijn indices
-- Compare this version to Par.Scoped
module DeBruijn.CPDT where

import Data.Type.Equality
import Util.Impl
import Util.Nat
import qualified Util.Stats as Stats
import Util.Syntax.ScopedDeBruijn

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "DeBruijn.CPDT",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nfd,
      impl_nfi = nfi,
      impl_aeq = (==)
    }

-------------------------------------------------------
{-
The classic implementation of substitution in de Bruijn terms requires an auxiliary operation, lifting, which increments the indices of all free variables in an expression. We need to lift whenever we "go under a binder." It is useful to write an auxiliary function liftVar that lifts a variable; that is, liftVar x y will return y + 1 if y >= x, and it will return y otherwise. This simple description uses numbers rather than our dependent fin family, so the actual specification is more involved.

Combining a number of dependent types tricks, we wind up with this concrete realization.
-}

liftVar :: Idx n -> Idx (Pred n) -> Idx n
liftVar FZ y = FS y
liftVar (FS _) FZ = FZ
liftVar (FS x') (FS y') = FS (liftVar x' y')

lift :: Term n -> Idx ('S n) -> Term ('S n)
lift e = case e of
  DVar f' -> \f -> DVar (liftVar f f')
  DApp e1 e2 -> \f -> DApp (lift e1 f) (lift e2 f)
  DLam e1 -> \f -> DLam (lift e1 (FS f))

nzf :: Idx n -> 'S (Pred n) :~: n
nzf FZ = Refl
nzf (FS _) = Refl

substVar :: Idx n -> Idx n -> Maybe (Idx (Pred n))
substVar FZ FZ = Nothing
substVar FZ (FS f') = Just f'
substVar (FS x') FZ
  | Refl <- nzf x' = Just FZ
substVar (FS x') (FS y')
  | Refl <- nzf y' = do
    f <- substVar x' y'
    Just $ FS f

subst :: Term n -> Idx n -> Term (Pred n) -> Term (Pred n)
subst e f v = case e of
  DVar f' -> case substVar f f' of
    Nothing -> v
    Just f'' -> DVar f''
  DApp e1 e2 -> DApp (subst e1 f v) (subst e2 f v)
  DLam e1 ->
    case (nzf f) of
      Refl -> DLam (subst e1 (FS f) (lift v FZ))

instantiate :: Term ('S n) -> Term n -> Term n
instantiate b a = subst b FZ a

-------------------------------------------------------

nfd :: Term n -> Term n
nfd e@(DVar _) = e
nfd (DLam b) = DLam (nfd b)
nfd (DApp f a) =
  case whnf f of
    DLam b -> nfd (instantiate b a)
    f' -> DApp (nfd f') (nfd a)

whnf :: Term n -> Term n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a

-------------------------------------------------------

nfi :: Int -> Term n -> Stats.M (Term n)
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam b) = DLam <$> nfi (n -1) b
nfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a

whnfi :: Int -> Term n -> Stats.M (Term n)
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n -1) f
  case whnf f' of
    DLam b -> Stats.count >> whnfi (n -1) (instantiate b a)
    _ -> return $ DApp f' a
