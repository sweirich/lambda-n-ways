{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}

-- | Well-scoped de Bruijn indices 
-- Doesn't use Rebound library (or bind type)
-- no bind type. evaluation based on substitution only
-- CBV beta-rule (i.e. whnormalizes before instantiate)

module Auto.Manual.Lazy.SubstV (toDB, impl) where

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

import Data.SNat as Nat
import Data.Fin
-- uses lazy scoped syntax
-- import Util.Syntax.Lazy.ScopedDeBruijn

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Auto.Manual.Lazy.SubstV",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = nf,
      impl_nfi = nfi,
      impl_aeq = (==),
      impl_eval = eval
    }

---------------------------------------------

data Exp n where
  DVar :: (Fin n) -> Exp n
  DLam :: (Bind n) -> Exp n
  DApp :: (Exp n) -> (Exp n) -> Exp n
  DBool :: Bool -> Exp n
  DIf :: Exp n -> Exp n -> Exp n -> Exp n

deriving instance Eq (Exp n)

instance NFData (Exp a) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (DBool b) = rnf b

data Bind n where
  Bind :: Exp (S n) -> Bind n

bind :: Exp (S n) -> Bind n
bind = Bind

unbind :: Bind n -> Exp (S n)
unbind (Bind a) = a

instance NFData (Bind n) where
  rnf b = rnf (unbind b)
  
instance Eq (Bind n) where
  b1 == b2 = unbind b1 == unbind b2

--------------------------------------------------

type Sub m n = Fin m -> Exp n                   

(.:) :: a -> (Fin m -> a) -> Fin (S m) -> a            -- extension
v .: r = \case { FZ -> v ; FS y -> r y } 

(.>>) :: Sub m n -> Sub p m -> Sub p n
r .>> s = apply r . s

up :: Sub m n -> Sub (S m) (S n)                       -- shift
up s = \case
          FZ -> DVar  FZ                               -- leave index 0 alone
          FS f -> apply (DVar . FS) (s f)              -- shift other indices
      
apply :: Sub m n -> Exp m -> Exp n                    -- multi substitutions
apply r (DVar x)      = r x
apply r (DLam (Bind b))      = 
  DLam (Bind (apply (up r) b))
apply r (DApp a1 a2)  = 
  DApp (apply r a1) (apply r a2)
apply r (DIf a b c)  = DIf (apply r a) (apply r b) (apply r c)
apply r (DBool b)     = DBool b

instantiate :: Bind n -> Exp n -> Exp n                  -- single substitution
instantiate (Bind b) v = apply (v .: DVar) b

----------------------------------------------------------

-- Evaluate closed terms with substitution
eval :: Exp Z -> Exp Z
eval (DVar x) = case x of {}
eval e@(DLam b) = e
eval (DApp f a) =
  case eval f of
    DLam b -> eval (instantiate b (eval a))
    _ -> error "type error"
eval (DBool b) = DBool b
eval (DIf a b c) = 
  case eval a of 
    DBool True -> eval b
    DBool False -> eval c
    _ -> error "type error"


----------------------------------------------------------

nf :: Exp n -> Exp n
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (unbind b)))
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b (whnf a))
    f' -> DApp (nf f') (nf a)
nf e@(DBool _) = e
nf (DIf a b c) = 
  case whnf a of 
    DBool True -> nf b
    DBool False -> nf c
    a' -> DIf (nf a') (nf b) (nf c)

whnf :: Exp n -> Exp n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> 
      whnf (instantiate b (whnf a))
    f' -> DApp f' a
whnf e@(DBool b) = DBool b
whnf (DIf a b c) = 
  case whnf a of 
    DBool True -> whnf b
    DBool False -> whnf c
    a' -> DIf a' b c


nfi :: Int -> Exp n -> Stats.M (Exp n)
nfi 0 _e = Stats.done
nfi _n e@(DVar _) = return e
nfi n (DLam e) = DLam . bind <$> nfi (n -1) (unbind e)
nfi n (DApp f a) = do
  f' <- whnfi (n - 1) f
  a' <- whnfi (n - 1) a
  case f' of
    DLam b -> Stats.count >> nfi (n -1) (instantiate b a')
    _ -> DApp <$> nfi (n - 1) f' <*> nfi (n - 1) a
nfi _ (DBool b) = return $ DBool b
nfi n (DIf a b c) = do
  a' <- whnfi (n - 1) a
  case a' of 
    DBool True -> nfi (n - 1) b
    DBool False -> nfi (n - 1) c
    a' -> DIf <$> (nfi (n-1) a') <*> (nfi (n-1) b) <*> (nfi (n-1) c)

whnfi :: Int -> Exp n -> Stats.M (Exp n)
whnfi 0 _e = Stats.done
whnfi _n e@(DVar _) = return e
whnfi _n e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n - 1) f
  a' <- whnfi (n-1) a
  case f' of
    DLam b -> Stats.count >> whnfi (n - 1) (instantiate b a')
    _ -> return $ DApp f' a
whnfi _ e@(DBool _) = return e
whnfi n (DIf a b c) = do
  a' <- whnfi (n-1) a
  case whnf a' of 
    DBool True -> whnfi (n - 1) b
    DBool False -> whnfi (n - 1) c
    a' -> return $ DIf a' b c

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
    to vs (Lam v b) = DLam (bind b')
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
    from n (DLam b) = Lam n (from (Prelude.succ n) (unbind b))
    from n (DApp f a) = App (from n f) (from n a)
    from n (DIf a b c) = If (from n a) (from n b) (from n c)
    from n (DBool b) = Bool b

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------
