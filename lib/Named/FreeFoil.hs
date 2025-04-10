{-# LANGUAGE LambdaCase #-}
module Named.FreeFoil where
-- adapted from https://hackage.haskell.org/package/free-foil-0.1.0/docs/src/Control.Monad.Foil.Example.html#Expr


import           Util.Impl (LambdaImpl(..))
import           Control.DeepSeq
import           Control.Monad.Foil
import           Control.Monad.Foil.Relative

-- $setup
-- >>> import Control.Monad.Foil

-- | Untyped \(\lambda\)-terms in scope @n@.
data Expr n where
  -- | Variables are names in scope @n@: \(x\)
  VarE :: Name n -> Expr n
  -- | Application of one term to another: \((t_1, t_2)\)
  AppE :: Expr n -> Expr n -> Expr n
  -- | \(\lambda\)-abstraction introduces a binder and a term in an extended scope: \(\lambda x. t\)
  LamE :: NameBinder n l -> Expr l -> Expr n
  BoolE :: Bool -> Expr n
  IfE :: Expr n -> Expr n -> Expr n -> Expr n


instance NFData (Expr l) where
  rnf (LamE binder body) = rnf binder `seq` rnf body
  rnf (AppE fun arg)     = rnf fun `seq` rnf arg
  rnf (VarE name)        = rnf name
  rnf (BoolE b) = rnf b
  rnf (IfE a b c) = rnf a `seq` rnf b `seq` rnf c
  

-- | This instance serves as a proof
-- that sinking of 'Expr' is safe.
instance Sinkable Expr where
  sinkabilityProof rename (VarE v) = VarE (rename v)
  sinkabilityProof rename (AppE f e) = AppE (sinkabilityProof rename f) (sinkabilityProof rename e)
  sinkabilityProof rename (LamE binder body) = extendRenaming rename binder $ \rename' binder' ->
    LamE binder' (sinkabilityProof rename' body)
  sinkabilityProof rename (BoolE b) = BoolE b
  sinkabilityProof rename (IfE a b c) = 
    IfE (sinkabilityProof rename a) 
        (sinkabilityProof rename b)
        (sinkabilityProof rename b)


instance InjectName Expr where
  injectName = VarE

-- | 'Expr' is a monad relative to 'Name'.
instance RelMonad Name Expr where
  rreturn = VarE
  rbind scope term subst =
    case term of
      VarE name -> subst name
      AppE x y  -> AppE (rbind scope x subst) (rbind scope y subst)
      LamE binder body ->
        withRefreshed scope (nameOf binder) $ \binder' ->
          let scope' = extendScope binder' scope
              subst' name = case unsinkName binder name of
                          Nothing -> rreturn (nameOf binder')
                          Just n  -> sink (subst n)
           in LamE binder' (rbind scope' body subst')
      BoolE b -> BoolE b
      IfE x y z  -> IfE (rbind scope x subst) (rbind scope y subst)
                       (rbind scope z subst)


-- | Substitution for untyped \(\lambda\)-terms.
-- The foil helps implement this function without forgetting scope extensions and renaming.
substitute :: Distinct o => Scope o -> Substitution Expr i o -> Expr i -> Expr o
substitute scope subst = \case
    VarE name -> lookupSubst subst name
    AppE f x -> AppE (substitute scope subst f) (substitute scope subst x)
    LamE binder body -> withRefreshed scope (nameOf binder) $ \binder' ->
      let subst' = addRename (sink subst) binder (nameOf binder')
          scope' = extendScope binder' scope
          body' = substitute scope' subst' body
       in LamE binder' body'
    BoolE b -> BoolE b
    IfE x y z -> IfE (substitute scope subst x) (substitute scope subst y) (substitute scope subst z)

-- | Compute weak head normal form (WHNF) of a \(\lambda\)-term.
--
-- >>> whnf emptyScope (AppE (churchN 2) (churchN 2))
-- λx1. (λx0. λx1. (x0 (x0 x1)) (λx0. λx1. (x0 (x0 x1)) x1))
whnf :: Distinct n => Scope n -> Expr n -> Expr n
whnf scope = \case
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst = addSubst identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> AppE fun' arg
  IfE scrut tru fls ->
    case whnf scope scrut of
      BoolE True -> whnf scope tru
      BoolE False -> whnf scope fls
      sc' -> IfE sc' tru fls
  t -> t

-- | Compute weak head normal form (WHNF) of a __closed__ \(\lambda\)-term.
--
-- >>> whnf' (AppE (churchN 2) (churchN 2))
-- λx1. (λx0. λx1. (x0 (x0 x1)) (λx0. λx1. (x0 (x0 x1)) x1))
whnf' :: Expr VoidS -> Expr VoidS
whnf' = whnf emptyScope

-- | Compute normal form (NF) of a \(\lambda\)-term.
--
-- >>> nf emptyScope (AppE (churchN 2) (churchN 2))
-- λx1. λx2. (x1 (x1 (x1 (x1 x2))))
nf :: Distinct n => Scope n -> Expr n -> Expr n
nf scope expr = case expr of
  LamE binder body ->
    -- Instead of using 'assertDistinct',
    -- another option is to add 'Distinct l' constraint
    -- to the definition of 'LamE'.
    case assertDistinct binder of
      Distinct ->
        let scope' = extendScope binder scope
        in LamE binder (nf scope' body)
  AppE fun arg ->
    case whnf scope fun of
      LamE binder body ->
        let subst = addSubst identitySubst binder arg
        in nf scope (substitute scope subst body)
      fun' -> AppE (nf scope fun') (nf scope arg)
  t -> t

-- | Compute normal form (NF) of a __closed__ \(\lambda\)-term.
--
-- >>> nf' (AppE (churchN 2) (churchN 2))
-- λx1. λx2. (x1 (x1 (x1 (x1 x2))))
nf' :: Expr VoidS -> Expr VoidS
nf' = nf emptyScope

impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.FreeFoil",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nf',
      impl_nfi = nfi,
      impl_aeq = aeq
    }

fromLC = undefined
toLC = undefined
nfi = undefined
aeq = undefined
