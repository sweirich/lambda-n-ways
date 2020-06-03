module Core.Nf where

import IdInt
import Lambda as LC
import Core.Core
import Core.Subst
import Core.CoreFVs
import Core.VarEnv
import Impl

impl :: LambdaImpl
impl = LambdaImpl {
             impl_name   = "Core"
           , impl_fromLC = id
           , impl_toLC   = id 
           , impl_nf     = nf
           , impl_nfi    = nfi
           , impl_aeq    = LC.aeq
        }

--- need to thunkify this if we want to have a correct comparison

nf :: LC IdInt -> LC IdInt
nf expr = go init_subst expr where
  init_subst = mkEmptySubst (mkInScopeSet (exprFreeVars expr))    
  go :: Subst -> LC IdInt -> LC IdInt
  go s (Var v) = lookupIdSubst ("nf") s v
  go s (Lam x b) = Lam y (go s' b) where
      (s', y) = substBndr s x
  go s (App f a) = 
      case go s f of 
        Lam x b -> do go s' b where
            s' = extendIdSubst s x (go s a)
        f' -> App f' (go s a)





whnf :: Subst -> LC IdInt -> LC IdInt
whnf s e@(Var v)   = lookupIdSubst ("whnf") s v
whnf s e@(Lam x b) = Lam y (substExpr "whnf" s' b) where
    (s', y) = substBndr s x
whnf s (App f a) =
    case whnf s f of
        Lam x b -> whnf (extendIdSubst s x a) b
        f' -> App f' a

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


