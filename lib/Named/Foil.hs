{-# LANGUAGE LambdaCase #-}
module Named.Foil where
-- adapted from https://hackage.haskell.org/package/free-foil-0.1.0/docs/src/Control.Monad.Foil.Example.html#Expr
-- and https://github.com/fizruk/free-foil/blob/main/haskell/lambda-pi/src/Language/LambdaPi/Impl/Foil.hs

import           Util.Impl (LambdaImpl(..))
import           Util.IdInt
import qualified Util.Syntax.Lambda as LC
import           Control.DeepSeq
import           Control.Monad.Foil
import           Control.Monad.Foil.Relative
import           Data.Map (Map)
import qualified Data.Map as Map

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
  IfE scrut tru fls ->
    case whnf scope scrut of
      BoolE True -> whnf scope tru
      BoolE False -> whnf scope fls
      sc' -> IfE sc' tru fls   
  t -> t

-- | Compute normal form (NF) of a __closed__ \(\lambda\)-term.
--
-- >>> nf' (AppE (churchN 2) (churchN 2))
-- λx1. λx2. (x1 (x1 (x1 (x1 x2))))
nf' :: Expr VoidS -> Expr VoidS
nf' = nf emptyScope

aeq :: Expr VoidS -> Expr VoidS -> Bool
aeq = alphaEquiv emptyScope

-- alpha-equivalence
alphaEquiv :: Distinct n => Scope n -> Expr n -> Expr n -> Bool
alphaEquiv scope e1 e2 = case (e1, e2) of
  (VarE x, VarE x') -> x == x'
  (AppE t1 t2, AppE t1' t2') -> alphaEquiv scope t1 t1' && alphaEquiv scope t2 t2'
  (BoolE b1, BoolE b2) -> b1 == b2
  (IfE t1 t2 t3, IfE t1' t2' t3') -> alphaEquiv scope t1 t1' && alphaEquiv scope t2 t2'
                                  && alphaEquiv scope t3 t3'
  (LamE x body, LamE x' body') -> case unifyPatterns x x' of
    SameNameBinders z    -> case assertDistinct z of
      Distinct -> alphaEquiv (extendScopePattern z scope) body body'
    RenameLeftNameBinder z renameL -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' (liftRM scope' (fromNameBinderRenaming renameL) body) body'
    RenameRightNameBinder z renameR -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' body (liftRM scope' (fromNameBinderRenaming renameR) body')
    RenameBothBinders z renameL renameR -> case assertDistinct z of
      Distinct ->
        let scope' = extendScopePattern z scope
        in alphaEquiv scope' (liftRM scope' (fromNameBinderRenaming renameL) body) (liftRM scope' (fromNameBinderRenaming renameR) body')
    NotUnifiable -> False
  _ -> False


-- | Convert a raw term into a scope-safe \(\lambda\Pi\)-term.
toFoilTerm
  :: Distinct n
  => Scope n                    -- ^ Target scope.
  -> Map IdInt (Name n)  -- ^ Mapping for variable names (to be extended with pattern).
  -> LC.LC IdInt                   -- ^ A raw term.
  -> Expr n
toFoilTerm scope env = \case
  LC.Var x ->
    case Map.lookup x env of
      Just name -> VarE name
      Nothing   -> error $ "unknown free variable: " <> show x

  LC.App t1 t2 ->
    AppE (toFoilTerm scope env t1) (toFoilTerm scope env t2)

  LC.Lam x body  ->
    withFresh scope $ \x' ->
      let env' = Map.insert x (nameOf x') (sink <$> env) 
          scope' = extendScope x' scope
      in LamE x' (toFoilTerm scope' env' body)
  LC.Bool b      -> BoolE b
  LC.If t1 t2 t3 -> IfE (toFoilTerm scope env t1) (toFoilTerm scope env t2) (toFoilTerm scope env t3)

fromLC :: LC.LC IdInt -> Expr VoidS
fromLC = toFoilTerm emptyScope Map.empty


fromFoilTerm
  :: [IdInt]         -- ^ A stream of fresh variable identifiers.
  -> NameMap n IdInt -- ^ A /total/ mapping for names in scope @n@.
  -> Expr n                 -- ^ A scope safe term in scope @n@.
  -> LC.LC IdInt
fromFoilTerm freshVars env = \case
  VarE name -> LC.Var (lookupName name env)
  AppE t1 t2 -> LC.App  (fromFoilTerm freshVars env t1) (fromFoilTerm freshVars env t2)
  LamE x body ->
    case freshVars of
        []   -> error "not enough fresh variables!"
        x':xs -> 
          let freshVars' = xs 
              env' = addNameBinder x x' env 
          in
             LC.Lam x' (fromFoilTerm freshVars' env' body)

toLC
  :: Expr VoidS       -- ^ A scope safe term in scope @n@.
  -> LC.LC IdInt
toLC = fromFoilTerm freshVars emptyNameMap
   where freshVars = [ fromInteger 0 ..]




impl :: LambdaImpl
impl =
  LambdaImpl
    { impl_name = "Named.Foil",
      impl_fromLC = fromLC,
      impl_toLC = toLC,
      impl_nf = nf',
      impl_nfi = nfi,
      impl_aeq = aeq,
      impl_eval = whnf'
    }

nfi = undefined

