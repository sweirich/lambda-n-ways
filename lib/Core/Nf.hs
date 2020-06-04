module Core.Nf where

import IdInt
import Lambda as LC
import Core.Core
import Core.Subst
import Core.CoreFVs
import Core.VarEnv
-- import extra modules to specialize/inline them
import Core.UniqSet
import Core.VarSet
import Core.UniqFM
import Core.Unique
import Impl

impl :: LambdaImpl
impl = LambdaImpl {
             impl_name   = "Core"
           , impl_fromLC = id
           , impl_toLC   = id 
           , impl_nf     = nf2
           , impl_nfi    = nfi
           , impl_aeq    = LC.aeq
        }

--- need to thunkify this if we want to have a correct comparison
-- or something

{-# SPECIALISE lookupUniqSet :: UniqSet (LC IdInt) -> IdInt -> Maybe (LC IdInt) #-}
{-# SPECIALISE lookupUFM     :: UniqFM (LC IdInt)  -> IdInt -> Maybe (LC IdInt) #-}

freshen :: LC IdInt -> LC IdInt
freshen e = substExpr "freshen" emptySubst e

-- This function works
-- but is it the same as the other versions?
-- and why is it soooo slow
nf :: LC IdInt -> LC IdInt
nf expr = go init_subst expr where
  init_subst = mkEmptySubst (mkInScopeSet (exprFreeVars expr))    
  -- INVARIANT: all terms that enter the range of the substitution
  -- have been normalized already
  go :: Subst -> LC IdInt -> LC IdInt
  go s (Var v)   = lookupIdSubst ("nf") s v
  go s (Lam x b) = Lam y (go s' b) where
      (s', y) = substBndr s x
  go s (App f a) = 
      case go s f of 
        Lam x b -> do go s' b where
            s' = extendIdSubst s x (go s a)
        f' -> App f' (go s a)

-- This is a closer version than `nf` but it is even slower
nf2 :: LC IdInt -> LC IdInt
nf2 expr = go init_subst expr where
  init_subst = mkEmptySubst (mkInScopeSet (exprFreeVars expr))
  -- INVARIANT: all terms that enter the range of the substitution
  -- have been normalized
  go :: Subst -> LC IdInt -> LC IdInt
  go s (Var v)   = lookupIdSubst ("nf") s v
  go s (Lam x b) = Lam y (go s' b) where
      (s', y) = substBndr s x
  go s (App f a) = 
      case whnf s f of 
        Lam x b -> go s' b where
            -- need a new subst as we have "appled" the current one already
            is = mkEmptySubst (substInScope s)
            s' = extendIdSubst is x (go s a)
        f' -> App f' (go s a)

  -- INVARIANT: the subst s has been applied to the entire term
  whnf :: Subst -> LC IdInt -> LC IdInt
  whnf s e@(Var v)   = lookupIdSubst ("whnf") s v
  whnf s e@(Lam x b) = Lam y (substExpr "whnf" s' b) where
      (s', y) = substBndr s x
  whnf s (App f a) =
      case whnf s f of
          Lam x b -> whnf s' b where
              is = mkEmptySubst (substInScope s)
              s' = extendIdSubst is x (go s a)
          f' -> App f' (substExpr "whnf" s a)

-----

nfi :: Int -> LC IdInt -> Maybe (LC IdInt)
nfi i expr = go i init_subst expr where
  init_subst = mkEmptySubst (mkInScopeSet (exprFreeVars expr))    
  go :: Int -> Subst -> LC IdInt -> Maybe (LC IdInt)
  go 0 _ _ = Nothing
  go i s (Var v) = return $ lookupIdSubst ("nf") s v
  go i s (Lam x b) = Lam y <$> go (i-1) s' b where
      (s', y) = substBndr s x
  go i s (App f a) = do
      f' <- go (i-1) s f
      case f' of 
        Lam x b -> do
          s' <- extendIdSubst s x <$> go (i-1) s a
          go (i-1) s' b
        _ -> App f' <$> go (i-1) s a


