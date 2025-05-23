{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
-- doesn't use Rebound library
-- explicit substitutions in arbitrary syntax nodes
module Auto.Manual.Lazy.ExplicitSubstV (toDB, impl) where

import Data.SNat as Nat
import Data.Fin
import Control.DeepSeq (NFData (..))
import Data.Maybe (fromJust)
import Text.PrettyPrint.HughesPJ
  ( Doc,
    parens,
    renderStyle,
    style,
    text,
    (<+>),
  )
import qualified Text.PrettyPrint.HughesPJ as PP
import Util.IdInt (IdInt (..), firstBoundId)
import Util.Impl (LambdaImpl (..))
import qualified Util.Stats as Stats
import Util.Syntax.Lambda (LC (..))

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Manual.Lazy.ExplicitSubstV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = error "NFI unimplemented",
      impl_aeq = (==),
      impl_eval = whnf
    }


data Exp n where
  DVar :: (Fin n) -> Exp n
  DLam :: (Exp (S n)) -> Exp n
  DApp :: (Exp n) -> (Exp n) -> Exp n
  DBool :: Bool -> Exp n
  DIf :: Exp n -> Exp n -> Exp n -> Exp n
  Sub :: Env m n -> Exp m -> Exp n


instance Eq (Exp n) where
  DVar x == DVar y = x == y
  DLam t == DLam u = t == u
  DApp t1 t2 == DApp u1 u2 = t1 == u1 && t2 == u2
  DBool x == DBool y = x == y
  DIf t1 t2 t3 == DIf u1 u2 u3 = t1 == u1 && t2 == u2 && t3 == u3
  Sub s t == Sub r u = apply s t == apply r u
  _ == _ = False

instance NFData (Exp a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (DBool b) = rnf b
  rnf (Sub r t) = rnf r `seq` rnf t

----------------------------------------------------------

type Env n m = Fin n -> Exp m

-- Apply a substitution to a term; composing 
-- with any explicit substitutions and pushing 
-- them one level down the syntax tree
-- Invariant: result of apply is *not* a Sub.
apply :: Env n m -> Exp n -> Exp m
apply s (DVar i) = s i
apply s (DLam b) = DLam (Sub (up s) b)
apply s (DApp f a) = DApp (Sub s f) (Sub s a)
apply s (DIf a b c) = DIf (Sub s a) (Sub s b) (Sub s c)
apply s (DBool b) = DBool b
apply s (Sub r t) = apply (s .>> r) t

idE :: Env m m
idE = DVar

nil :: Fin Z -> a
nil = \case

(.:) :: a -> (Fin m -> a) -> Fin (S m) -> a               -- extension
v .: r = \case { FZ -> v ; FS y -> r y } 

(.>>) :: Env m n -> Env p m -> Env p n
r .>> s = apply r . s

up :: Env m n -> Env (S m) (S n)             -- shift
up s = \case
          FZ -> DVar  FZ                     -- leave index 0 alone
          FS f -> apply (DVar . FS) (s f)    -- shift other indices

singleton :: Exp m -> Env (S m) m
singleton a = a .: idE
----------------------------------------------------

-- result of nf is not a Sub
nf :: Exp n -> Exp n
nf e@(DVar _) = e
nf (DLam b) = DLam (nf b)
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (apply (singleton (whnf a)) b)
    f' -> DApp (nf f') (nf a)
nf (DIf a b c) =
  case whnf a of 
    DBool True -> nf b
    DBool False -> nf c
    a' -> DIf (nf a') (nf b) (nf c)
nf (DBool b) = DBool b
nf (Sub r t) = nf (apply r t)

-- result of whnf is NOT a Sub
whnf :: Exp n -> Exp n
whnf e@(DVar x) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b' -> 
        whnf (apply (singleton (whnf a)) b')
    f' -> DApp f' a
whnf (DBool b) = DBool b
whnf (DIf a b c) = case whnf a of 
  DBool True -> whnf b
  DBool False -> whnf c
  a' -> DIf a' b c
whnf (Sub s t) = whnf (apply s t)


---------------------------------------------------------
{-
Convert to deBruijn indicies.  Do this by keeping a list of the bound
variable so the depth can be found of all variables. NOTE: input term
must be closed or 'fromJust' will error.
-}

toDB :: LC IdInt -> Exp 'Z
toDB = to []
  where
    to :: [(IdInt, Fin n)] -> LC IdInt -> Exp n
    to vs (Var v) = DVar (fromJust (lookup v vs))
    to vs (Lam v b) = DLam b'
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)
    to vs (If a b c) = DIf (to vs a) (to vs b) (to vs c)
    to vs (Bool b) = DBool b

-- Convert back from deBruijn to the LC type.

fromDB :: Exp n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Exp n -> LC IdInt
    from (IdInt n) (DVar i)
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DLam b) = Lam n (from (Prelude.succ n) b)
    from n (DApp f a) = App (from n f) (from n a)
    from n (DIf a b c) = If (from n a) (from n b) (from n c)
    from n (DBool b) = Bool b
    from n (Sub s b) = from n (apply s b)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------
