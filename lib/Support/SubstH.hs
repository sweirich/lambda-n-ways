{-# LANGUAGE DefaultSignatures #-}
module Support.SubstH 
    (Var(..), 
    Bind, bind, unbind, freeVarsBind, substBind,
    validBind,
    VarSet, 
    Sub, emptySub, singleSub, comp,
    VarC(..),
    FreeVarsC(..),
    SubstC(..),
    instantiate)
    where

import Util.IdInt (IdInt)
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Imports ( NFData(..) ) 
import GHC.Generics

-------------------------------------------
newtype Var = V IdInt deriving (Show, Eq, NFData, Generic)

type VarSet = S.IdIntSet
type Sub = M.IdIntMap

-- In this implementation we cache substitutions and fv sets at binders.
-- That means that we can combine substitutions together.
-- NOTE: the cached substitution *has not* been applied to the binder.
-- so this means that we haven't yet done any renaming of the binder (to avoid capture)
-- or pruning of the substitution (to cut off substitution early).
data Bind e = Bind
  { bind_subst :: !(Sub e),
    bind_fvs   :: !(VarSet),
    bind_var   :: !IdInt,
    bind_body  :: !e
  }

{-
Invariants for bind:

1. bind_fvs is cached freeVars of e, minus v

3. The domain of the bind_subst is a subset of bind_fvs

3. The freeVars of the bind_subst do not include v (i.e. they will not capture).
   (If this would happen when constructing a bind, we will freshen v to v'
   and extend the substitution with v -> v', in the case that v is free in e.)
-}

-------------------------------------------------------------------

class VarC a where
   var :: Var -> a 

   isvar :: a -> Maybe Var
   isvar _ = Nothing
   {-# INLINE isvar #-}

class FreeVarsC a where
   freeVars :: a -> VarSet

   default freeVars :: (Generic a, GFreeVars (Rep a), VarC a) => a -> VarSet
   freeVars x =
     case (isvar x) of
         Just (V v)  -> S.singleton v
         Nothing -> gfreeVars (from x)

class FreeVarsC a => SubstC b a where
   subst :: Sub b -> a -> a
   default subst :: (Generic a, GSubst b (Rep a), VarC a, a ~ b) => Sub b -> a -> a
   subst s x =
     case (isvar x) of
         Just (V i)  -> M.findWithDefault x i s
         Nothing -> to $ gsubst s (from x)
   {-# INLINE subst #-}

-------------------------------------------------------------------

instantiate :: (VarC a, SubstC a a) => Bind a -> a -> a
instantiate b u = subst (singleSub y u) a  where
    (y,a) = unbind b

-------------------------------------------------------------------
-- varset operations

lookupMax :: VarSet -> Maybe IdInt
lookupMax vs = if S.null vs then Nothing else Just $ S.findMax vs
{-# INLINEABLE lookupMax #-}

varSetMax :: VarSet -> IdInt
varSetMax s = maybe (toEnum 0) succ (lookupMax s)
{-# INLINEABLE varSetMax #-}   

-------------------------------------------------------------------
-- sub operations

emptySub :: Sub e
emptySub = M.empty
{-# INLINEABLE emptySub #-}

singleSub :: Var -> e -> Sub e
singleSub (V x) = M.singleton x
{-# INLINEABLE singleSub #-}

comp :: SubstC a a => Sub a -> Sub a -> Sub a
comp s1 s2
  | M.null s1 = s2
  | M.null s2 = s1
  -- union is left biased. We want the value from s2 if there is also a definition in s1
  -- but we also want the range of s2 to be substituted by s1
  | otherwise = substSub s1 s2 <> s1
{-# INLINEABLE comp #-}

freeVarsSub :: FreeVarsC a => Sub a -> S.IdIntSet
freeVarsSub = foldMap freeVars
{-# INLINEABLE freeVarsSub #-}

substSub :: (Functor f, SubstC b a) => Sub b -> f a -> f a
substSub s2 s1 = fmap (subst s2) s1
{-# INLINEABLE substSub #-}

--------------------------------------------------------
-- bind operations

validBind :: (FreeVarsC a, Eq a) => Bind a -> Bool
validBind b@Bind {} =
  bind_fvs b == S.delete (bind_var b) (freeVars (bind_body b))

bind :: (FreeVarsC a) => Var -> a -> Bind a
bind (V v) a = Bind emptySub (S.delete v (freeVars a)) v a
{-# INLINEABLE bind #-}

unbind :: (VarC a, SubstC a a) => Bind a -> (Var, a)
unbind b = (V y, subst s a)
  where
    (y, s, a) = unbindHelper b
{-# INLINEABLE unbind #-}

-- | This part does the dirty work with pushing a substitution through
-- the binder. It returns but does not actually apply the substitution.
-- 1. renaming bound variable to avoid capture
-- 2. pruning the substitution to terminate early
unbindHelper :: (VarC a, SubstC a a) => Bind a -> (IdInt, Sub a, a)
unbindHelper (Bind s fv x a)
  -- fast-path
  | M.null s = (x, s, a)
  -- alpha-vary if in danger of capture
  | x `S.member` fv_s = (y, M.insert x (var (V y)) s', a)
  -- usual case, but prune substitution
  | otherwise = (x, s', a)
  where
    -- restrict to the free variables of the term
    s' = M.restrictKeys s fv
    fv_s = freeVarsSub s'
    y = maximum (fmap varSetMax [fv, fv_s])
{-# INLINEABLE unbindHelper #-}
 
instance (NFData a) => NFData (Bind a) where
  rnf (Bind s f x a) = rnf s `seq` rnf f `seq` rnf x `seq` rnf a

instance (Eq a, SubstC a a, VarC a) => Eq (Bind a) where
  b1 == b2
     | x1 == x2 = 
        -- apply delayed substs if variable names are the same
       subst s1 a1 == subst s2 a2
     | x1 `S.member` freeVarsBind b2 = False
     | x2 `S.member` freeVarsBind b1 = False
     | otherwise = subst s1 a1 == subst s2' a2
   where
     s2' = M.singleton x2 (var (V x1)) `comp` s2 
     (x1, s1, a1) = unbindHelper b1
     (x2, s2, a2) = unbindHelper b2



freeVarsBind :: (VarC a, SubstC a a) => Bind a -> S.IdIntSet
freeVarsBind b = freeVarsSub s <> (bind_fvs b S.\\ M.keysSet s)
  where
    (_, s, _) = unbindHelper b
{-# INLINEABLE freeVarsBind #-}

substBind :: (VarC a, SubstC a a) => Sub a -> Bind a -> Bind a
substBind s2 b@(Bind s1 _fv _x _a)
  | M.null s2 = b
  -- forcing this substitution, instead of delaying it,  seems to be particularly
  -- important for the lennart/nf benchmark. (14.0 sec -> 0.11 sec)
  | M.null s1 = bind (V x) (subst s' a)
  where
    (x, s', a) = unbindHelper (b {bind_subst = s2})
{-
  bind y a'
  where
    s' = M.restrictKeys s2 fv
    fv_s = freeVarsSub s'
    (y, a') =
      if M.null s'
        then (x, a)
        else
          if x `S.member` fv_s
            then -- is this fresh enough? what if we pick a variable that is already
            -- in scope? as long as it doesn't appear free, it is ok to shadow it.
            -- \x. \z. ((\y. \x. y) x)  --> \x. \z. (\z. x)

              let y = maximum (fmap varSetMax [fv, fv_s])
               in let s'' = M.insert x (Var y) s'
                   in (y, subst s'' a)
            else (x, subst s2 a) -}
substBind s2 b@(Bind s1 _fv _x _e) = b {bind_subst = s2 `comp` s1}

-------------------------------------------------------------------
class GFreeVars f where
  gfreeVars :: f a -> VarSet

class GSubst b f where
  gsubst :: Sub b -> f a -> f a  
  

-- Constant types
instance (SubstC b c) => GSubst b (K1 i c) where
  gsubst s (K1 c) = K1 (subst s c) 

instance GSubst b U1 where
  gsubst _s U1 = U1

instance GSubst b f => GSubst b (M1 i c f) where
  gsubst s = M1 . gsubst s . unM1
  {-# INLINE gsubst #-}

instance GSubst b V1 where
  gsubst _s = id
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst s (f :*: g) = gsubst s f :*: gsubst s g
  {-# INLINE gsubst #-}

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst s (L1 f) = L1 $ gsubst s f
  gsubst s (R1 g) = R1 $ gsubst s g
  {-# INLINE gsubst #-}

newtype Ignore a = Ignore a 

instance SubstC b (Ignore a) where
  subst _ = id
  {-# INLINE subst #-}
  
instance SubstC b Int where
  subst _ = id
  {-# INLINE subst #-}
instance SubstC b Bool where
  subst _ = id
  {-# INLINE subst #-}
instance SubstC b () where
  subst _ = id
  {-# INLINE subst #-}
instance SubstC b Char where
  subst _ = id
  {-# INLINE subst #-}


instance SubstC b Var where
  subst _ = id
  {-# INLINE subst #-}  
instance (VarC b, SubstC b b) => SubstC b (Bind b) where
  subst = substBind 
  {-# INLINE subst #-}

instance (Generic a, FreeVarsC a, GSubst b (Rep [a])) => SubstC b [a] where
  subst s x = to $ gsubst s (from x)
instance (Generic a, FreeVarsC a, GSubst b (Rep (Maybe a))) => SubstC b (Maybe a) where
  subst s x = to $ gsubst s (from x)
instance (Generic (Either a1 a2), FreeVarsC (Either a1 a2), GSubst b (Rep (Either a1 a2))) => SubstC b (Either a1 a2) where
  subst s x = to $ gsubst s (from x)
instance (Generic (a, b), FreeVarsC (a,b), GSubst c (Rep (a,b))) => SubstC c (a, b) where
  subst s x = to $ gsubst s (from x)
instance (Generic (a, b, d), FreeVarsC (a,b,d), 
    GSubst c (Rep (a,b,d))) => SubstC c (a, b, d) where
  subst s x = to $ gsubst s (from x)

----------------------------------------------------------------


instance (FreeVarsC c) => GFreeVars (K1 i c) where
  gfreeVars (K1 c) = (freeVars c) 

instance GFreeVars U1 where
  gfreeVars U1 = S.empty

instance GFreeVars f => GFreeVars (M1 i c f) where
  gfreeVars = gfreeVars . unM1
  {-# INLINE gfreeVars #-}

instance GFreeVars V1 where
  gfreeVars _s = S.empty
  {-# INLINE gfreeVars #-}

instance (GFreeVars f, GFreeVars g) => GFreeVars (f :*: g) where
  gfreeVars (f :*: g) = gfreeVars f `S.union` gfreeVars g
  {-# INLINE gfreeVars #-}

instance (GFreeVars f, GFreeVars g) => GFreeVars (f :+: g) where
  gfreeVars (L1 f) = gfreeVars f
  gfreeVars (R1 g) = gfreeVars g
  {-# INLINE gfreeVars #-}

instance FreeVarsC (Ignore a) where
  freeVars _ = S.empty
  {-# INLINE freeVars #-}
  
instance FreeVarsC Int where
  freeVars _ = S.empty
  {-# INLINE freeVars #-}
instance FreeVarsC Bool where
  freeVars _ = S.empty
  {-# INLINE freeVars #-}
instance FreeVarsC () where
  freeVars _ = S.empty
  {-# INLINE freeVars #-}
instance FreeVarsC Char where
  freeVars _ = S.empty
  {-# INLINE freeVars #-}
instance FreeVarsC String where
  freeVars _ = S.empty
  {-# INLINE freeVars #-}

instance FreeVarsC Var where
  freeVars _ = S.empty
  {-# INLINE freeVars #-}  

instance (VarC b, SubstC b b) => FreeVarsC (Bind b) where
  freeVars = freeVarsBind 
  {-# INLINE freeVars #-}

instance (Generic a, GFreeVars (Rep [a])) => FreeVarsC [a] where
  freeVars x = gfreeVars (from x)
instance (Generic a, GFreeVars (Rep (Maybe a))) => FreeVarsC (Maybe a) where
  freeVars x = gfreeVars (from x)
instance (Generic (Either a1 a2), GFreeVars (Rep (Either a1 a2))) => FreeVarsC (Either a1 a2) where
  freeVars x = gfreeVars (from x)
instance (Generic (a, b), GFreeVars (Rep (a,b))) => FreeVarsC (a, b) where
  freeVars x = gfreeVars (from x)
instance (Generic (a, b, d),GFreeVars  (Rep (a,b,d))) => FreeVarsC (a, b, d) where
  freeVars x = gfreeVars (from x)