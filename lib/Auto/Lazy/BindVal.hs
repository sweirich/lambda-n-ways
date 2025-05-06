{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}


-- | Uses the Autoenv library, with a lazy datatype
-- The whnf function does not include an explicit environment argument
module Auto.Lazy.BindVal (toDB, impl) where

import AutoEnv
import AutoEnv.Bind.Single
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
    { impl_name = "Auto.Lazy.BindVal",
      impl_fromLC = toDB,
      impl_toLC = fromDB,
      impl_nf = error "unimplemented",
      impl_nfi = error "unimplemented",
      impl_aeq = (==),
      impl_eval = DVal . eval
    }

data Val n where
  DVar :: Fin n -> Val n
  DLam :: Bind Val Exp n -> Val n
  DBool :: Bool -> Val n
  
data Exp n where
  DVal :: (Val n) -> Exp n
  DApp :: (Exp n) -> (Exp n) -> Exp n
  DIf :: Exp n -> Exp n -> Exp n -> Exp n
-- standalone b/c GADT
-- alpha equivalence is (==)
deriving instance Eq (Exp n)
deriving instance Eq (Val n)

instance Eq (Bind Val Exp n) where
  b1 == b2 = getBody b1 == getBody b2

instance NFData (Val n) where
  rnf (DVar i) = rnf i
  rnf (DLam d) = rnf d
  rnf (DBool b) = rnf b
instance NFData (Exp a) where
  rnf (DVal a) = rnf a
  rnf (DApp a b) = rnf a `seq` rnf b
  rnf (DIf a b c) = rnf a `seq` rnf b `seq` rnf c

instance (Subst v e, forall n. NFData (e n)) => NFData (Bind v e n) where
  rnf b = rnf (getBody b)

----------------------------------------------------------
-- uses the SubstScoped library
instance SubstVar Val where
  var = DVar
  {-# INLINEABLE var #-}

instance Subst Val Val where
  applyE s (DVar i) = applyEnv s i
  applyE s (DLam b) = DLam (applyE s b)
  applyE s (DBool b) = DBool b
instance Subst Val Exp where
  applyE s (DVal x) = DVal (applyE s x)
  applyE s (DApp f a) = DApp (applyE s f) (applyE s a)
  applyE s (DIf a b c) = DIf (applyE s a) (applyE s b) (applyE s c)
  {-# INLINEABLE applyE #-}

{-# SPECIALIZE applyEnv :: Env Val n m -> Fin n -> Val m #-}

{-# SPECIALIZE idE :: Env Val n n #-}

{-# SPECIALIZE (.>>) :: Env Val m n -> Env Val n p -> Env Val m p #-}

{-# SPECIALIZE up :: Env Val n m -> Env Val ('S n) ('S m) #-}

{-# SPECIALIZE getBody :: Bind Val Exp n -> Exp ('S n) #-}

{-# SPECIALIZE instantiate :: Bind Val Exp n -> Val  n -> Exp  n #-}

{-# SPECIALIZE bind :: Exp (S n) -> Bind Val Exp n #-}

----------------------------------------------------------

{-

nf :: Exp n -> Exp n
nf e@(DVar _) = e
nf (DLam b) = DLam (bind (nf (getBody b)))
nf (DApp f a) =
  case whnf f of
    DLam b -> nf (instantiate b a)
    f' -> DApp (nf f') (nf a)
nf e@(DBool _) = e
nf (DIf a b c) = 
  case whnf a of 
    DBool True -> nf a
    DBool False -> nf b
    a' -> DIf (nf a) (nf b) (nf c)

whnf :: Exp n -> Exp n
whnf e@(DVar _) = e
whnf e@(DLam _) = e
whnf (DApp f a) =
  case whnf f of
    DLam b -> whnf (instantiate b a)
    f' -> DApp f' a
whnf e@(DBool b) = DBool b
whnf (DIf a b c) = 
  case whnf a of 
    DBool True -> whnf b
    DBool False -> whnf c
    a' -> DIf a' b c
    
-}

eval :: Exp Z -> Val Z
eval e@(DVal v) = v
eval (DApp f a) =
  case eval f of
    DLam b -> eval (instantiate b (eval a)) 
    DVar x -> case x of {}
    DBool b -> error "type error"
eval (DIf a b c) = 
  case eval a of 
    DBool True -> eval b
    DBool False -> eval c
    DVar x -> case x of {}
    DLam b -> error "type error"

---------------------------------------------------------------

{-
nfi :: Int -> Val  n -> Stats.M (Val  n)
nfi 0 _ = Stats.done
nfi _ e@(DVar _) = return e
nfi n (DLam b) = DLam . bind <$> nfi (n - 1) (getBody b)
nfi n (DApp f a) = do
  f' <- whnfi (n - 1) f
  case f' of
    DLam b -> Stats.count >> nfi (n - 1) (instantiate b a)
    _ -> DApp <$> nfi n f' <*> nfi n a
nfi n (DBool b) = return (DBool b)
nfi n (DIf a b c) = do
  a' <- whnfi (n - 1) a
  case a' of 
    DBool True -> nfi (n -1) b
    DBool False -> nfi (n -1) c
    _ -> DIf <$> nfi (n-1) a' <*> nfi (n-1) b <*> nfi (n -1) c 
whnfi :: Int -> Val  n -> Stats.M (Val  n)
whnfi 0 _ = Stats.done
whnfi _ e@(DVar _) = return e
whnfi _ e@(DLam _) = return e
whnfi n (DApp f a) = do
  f' <- whnfi (n - 1) f
  case whnf f' of
    DLam b -> Stats.count >> whnfi (n - 1) (instantiate b a)
    _ -> return $ DApp f' a
whnfi n (DBool b) = return (DBool b)
whnfi n (DIf a b c) = do
  a' <- whnfi (n - 1) a
  case a' of 
    DBool True -> whnfi (n -1) b
    DBool False -> whnfi (n -1) c
    _ -> DIf <$> whnfi (n-1) a' <*> whnfi (n-1) b <*> whnfi (n -1) c 
-}

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
    to vs (Var v) = DVal (DVar (fromJust (lookup v vs)))
    to vs (Lam v b) = DVal (DLam (bind b'))
      where
        b' = to ((v, FZ) : mapSnd FS vs) b
    to vs (App f a) = DApp (to vs f) (to vs a)
    to vs (Bool b)  = DVal (DBool b)
    to vs (If a b c) = DIf (to vs a) (to vs b) (to vs c)
-- Convert back from deBruijn to the LC type.

fromDB :: Exp n -> LC IdInt
fromDB = from firstBoundId
  where
    from :: IdInt -> Exp n -> LC IdInt
    from (IdInt n) (DVal (DVar i))
      | toInt i < 0 = Var (IdInt $ toInt i)
      | toInt i >= n = Var (IdInt $ toInt i)
      | otherwise = Var (IdInt (n - toInt i - 1))
    from n (DVal (DLam b)) = Lam n (from (Prelude.succ n) (getBody b))
    from n (DApp f a) = App (from n f) (from n a)
    from n (DVal (DBool b)) = Bool b
    from n (DIf a b c) = If (from n a) (from n b) (from n c)

mapSnd :: (a -> b) -> [(c, a)] -> [(c, b)]
mapSnd f = map (\(v, i) -> (v, f i))

---------------------------------------------------------

