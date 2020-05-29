module Core.Nf where

import IdInt
import Lambda as LC
import Core.Core
import Core.Subst
import Core.CoreFVs
import Core.VarEnv

-- 

nf :: LC IdInt -> LC IdInt
nf expr = go init_subst expr where
  init_subst = mkEmptySubst (mkInScopeSet (exprFreeVars expr))    
  go :: Subst -> LC IdInt -> LC IdInt
  go s (Var v) = lookupIdSubst ("nf") s v
  go s (Lam x b) = Lam y (go s' b) where
      (s', y) = substBndr s x
  go s (App f a) = 
      case whnf s f of 
        Lam x b -> go s' b where
            s' = extendIdSubst s x (go s a)
        f' -> App (go s f') (go s a)

whnf :: Subst -> LC IdInt -> LC IdInt
whnf s e@(Var v)   = lookupIdSubst ("whnf") s v
whnf s e@(Lam x b) = Lam y (substExpr "whnf" s' b) where
    (s', y) = substBndr s x
whnf s (App f a) =
    case whnf s f of
        Lam x b -> whnf (extendIdSubst s x a) b
        f' -> App f' a