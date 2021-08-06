{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

{-

Generic definition of a lambda calculus datatype, parameterized by a binding
implementation.

For full flexibility, all of the operations of the binding implementation are
given a monadic interface, specifiable by the implementation.

 -}

module Abstract.Class
  ( LC (..),
    BindingImpl (..),
    genScoped,
    shrinkScoped,
    maxBindingDepth,
    depth,
    size,
    nf,
    nfm,
    instrNormalize,
    lam,
    lam',
    bind',
    unbind',
    St (..),
    module Imports,
    module IdInt,
  )
where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.List (union, (\\))
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Text.ParserCombinators.ReadP as RP
import qualified Text.PrettyPrint.HughesPJ as PP
import Util.IdInt
import Util.Imports

-- Datatype for lambda calculus terms, parameterized by
-- a "binding implmentation v" (See Impl class below).

data LC v = Var !v | Lam !(Bind v) | App !(LC v) !(LC v)
  deriving (Generic)

class
  ( Arbitrary v,
    Ord v,
    NFData v,
    Read v,
    Show v,
    NFData (Bind v)
  ) =>
  BindingImpl v
  where
  type Bind v :: Type
  type Scope v :: Type
  type Subst v :: Type

  -- Scope operations
  topLevel :: Scope v
  inScope :: v -> Scope v -> Bool
  next :: Scope v -> (v, Scope v)

  -- Bind operations
  bind :: v -> LC v -> Scope v -> Bind v
  unbind :: Bind v -> Scope v -> (v, LC v)

  -- Sub operations
  singleton :: v -> LC v -> Subst v
  subst :: Subst v -> LC v -> Scope v -> (LC v)

  aeq :: LC v -> LC v -> Scope v -> Bool

  -- some implementations may choose to override this definition with something
  -- faster
  instantiate :: Bind v -> LC v -> Scope v -> LC v
  instantiate b a = do
    (x, e) <- unbind b
    subst (singleton x a) e

  toLC :: LC v -> Scope v -> (LC IdInt)
  fromLC :: LC IdInt -> (Scope v -> LC v)

instance (NFData a, NFData (Bind a)) => NFData (LC a)

instance BindingImpl v => Eq (LC v) where
  (==) = \x y -> runBindM @v (aeq x y)

lam :: BindingImpl v => v -> LC v -> Scope v -> LC v
lam v e = Lam <$> bind v e

----------------------------------------------------------------------------
-- Normal order reduction
-- Don't reduce arguments before substitution
nf :: forall v. BindingImpl v => LC v -> LC v
nf e = (nf' @v e) (topLevel @v)

nf' :: forall v. BindingImpl v => LC v -> Scope v -> (LC v)
nf' e@(Var _) = return e
nf' (Lam b) = do
  (x, e) <- unbind @v b
  e' <- nf' e
  Lam <$> bind x e'
nf' (App f a) = do
  f' <- whnf f
  case f' of
    Lam b -> do
      a' <- instantiate b a
      nf' a'
    f' -> App <$> nf' f' <*> nf' a

whnf :: BindingImpl v => LC v -> Scope v -> (LC v)
whnf e@(Var _) = return e
whnf e@(Lam _) = return e
whnf (App f a) = do
  f' <- whnf f
  case f' of
    Lam b -> do
      a' <- instantiate b a
      whnf a'
    f' -> return $ App f' a

----------------------------------------------------------------------------
-- "Fueled" version of normal-order reduction
-- Also counts the number of substitutions

newtype St = St {numSubsts :: Int}

type BindM v = (->) (Scope v)

runBindM :: forall v a. BindM v a -> a
runBindM f = f (topLevel @v)

type M v a = StateT St (ExceptT String (BindM v)) a

liftBindM :: forall v a. BindingImpl v => BindM v a -> M v a
liftBindM x = lift (lift x)

instrNormalize :: forall v. BindingImpl v => Int -> LC v -> Maybe (LC v)
instrNormalize i z = fst <$> either (const Nothing) Just (runBindM @v m3)
  where
    m3 :: BindM v (Either String (LC v, St))
    m3 = runExceptT m2
    m2 :: ExceptT String (BindM v) (LC v, St)
    m2 = runStateT m1 (St 0)
    m1 :: StateT St (ExceptT String (BindM v)) (LC v)
    m1 = nfm i z

{-
  fst
    <$> either
      (const Nothing)
      Just
      (runStateT (nfm i z) (St 0))
-}

instrSubst :: forall v. BindingImpl v => v -> LC v -> LC v -> M v (LC v)
instrSubst x a b = do
  s <- get
  put (s {numSubsts = numSubsts s + 1})
  liftBindM @v $ subst (singleton x a) b

instrInstantiate :: forall v. (BindingImpl v) => Bind v -> LC v -> M v (LC v)
instrInstantiate b a = do
  s <- get
  put (s {numSubsts = numSubsts s + 1})
  liftBindM @v $ instantiate b a

nfm ::
  forall v.
  (BindingImpl v) =>
  Int ->
  LC v ->
  M v (LC v)
nfm 0 _e = throwError "oops"
nfm _n e@(Var _) = return e
nfm n (Lam b) = do
  (x, e) <- liftBindM @v $ unbind @v b
  e' <- nfm (n - 1) e
  b' <- liftBindM @v $ bind x e'
  return (Lam b')
nfm n (App f a) = do
  f' <- whnfm (n - 1) f
  case f' of
    Lam b -> do
      b' <- instrInstantiate b a
      nfm (n -1) b'
    _ -> App <$> nfm (n -1) f' <*> nfm (n -1) a

whnfm ::
  forall v.
  (BindingImpl v) =>
  Int ->
  LC v ->
  M v (LC v)
whnfm 0 _e = throwError "oops"
whnfm _n e@(Var _) = return e
whnfm _n e@(Lam _) = return e
whnfm n (App f a) = do
  f' <- whnfm (n - 1) f
  case f' of
    Lam b -> do
      b' <- instrInstantiate b a
      whnfm (n - 1) b'
    _ -> return $ App f' a

----------------------------------------------------------------------------
-- Misc

maxBindingDepth :: forall v. (BindingImpl v) => LC v -> Int
maxBindingDepth a = runBindM @v (go a)
  where
    go (Var _v) = return 0
    go (Lam b) = do
      (_v, t) <- unbind b
      (1 +) <$> go t
    go (App t s) = max <$> go t <*> go s

depth :: forall v. BindingImpl v => LC v -> Int
depth a = runBindM @v (go a)
  where
    go (Var _v) = return 0
    go (Lam b) = do
      (_v, t) <- unbind b
      (1 +) <$> go t
    go (App t s) = (1 +) <$> (max <$> go t <*> go s)

size :: forall v. BindingImpl v => LC v -> Int
size a = runBindM @v (go a)
  where
    go (Var _v) = return 1
    go (Lam b) = do
      (_v, t) <- unbind b
      (1 +) <$> go t
    go (App t s) = do
      t' <- go t
      s' <- go s
      return $ 1 + t' + s'

---------------------------- Read/Show -------------------------------------

instance (BindingImpl v) => Read (LC v) where
  readsPrec _ = RP.readP_to_S pLC

pLC,
  pLCAtom,
  pLCVar,
  pLCLam,
  pLCApp ::
    forall v.
    (BindingImpl v) =>
    ReadP (LC v)
pLC = pLCLam RP.+++ pLCApp RP.+++ pLCLet
pLCVar = Var <$> pVar
pLCLam = do
  _ <- schar '\\'
  v <- pVar
  _ <- schar '.'
  e <- (pLC :: ReadP (LC v))
  return $ Lam (runBindM @v (bind v e))
pLCApp = do
  es <- RP.many1 pLCAtom
  return $ foldl1 App es
pLCAtom = pLCVar RP.+++ (do _ <- schar '('; e <- pLC; _ <- schar ')'; return e)

pLCLet :: forall v. (BindingImpl v) => ReadP (LC v)
pLCLet = do
  let lcLet (x, e) b = App (Lam (runBindM @v (bind x b))) e
      pDef = do
        v <- pVar
        _ <- schar '='
        e <- pLC
        return (v, e)
  _ <- sstring "let"
  bs <- RP.sepBy pDef (schar ';')
  _ <- sstring "in"
  e <- pLC
  return $ foldr lcLet e bs

{-
newtype ReadM v a = ReadM (BindM v (ReadP a))

instance BindingImpl v => Functor (ReadM v)

instance BindingImpl v => Applicative (ReadM v)

instance BindingImpl v => Monad (ReadM v) where
  return x = ReadM (return (return x))
  (ReadM m) >>= k = ReadM (m >>= undefined)

(+++) :: BindingImpl v => ReadM v a -> ReadM v a -> ReadM v a
(ReadM m1) +++ ReadM m2 = ReadM $ do
  x1 <- m1
  x2 <- m2
  return $ x1 RP.+++ x2

liftP :: ReadP a -> ReadM v a
liftP m = ReadM (return m)

rpLC,
  rpLCAtom,
  rpLCVar,
  rpLCLam,
  rpLCApp ::
    forall v.
    (BindingImpl v) =>
    ReadM v (LC v)
rpLC = rpLCLam +++ rpLCApp +++ rpLCLet
rpLCVar = Var <$> liftP pVar
rpLCLam = do
  v <- liftP $ do
    _ <- schar '\\'
    v <- pVar
    _ <- schar '.'
    return v
  e <- rpLC
  b <- ReadM $ bind v e
  return $ Lam b
rpLCApp = do
  es <- RP.many1 rpLCAtom
  return $ foldl1 App es
rpLCAtom = rpLCVar RP.+++ (do _ <- schar '('; e <- rpLC; _ <- schar ')'; return e)

rpLCLet :: forall v. (BindingImpl v) => ReadM v (LC v)
rpLCLet = do
  let lcLet (x, e) b = App (Lam (runBindM @v (bind x b))) e
      pDef = do
        v <- pVar
        _ <- schar '='
        e <- rpLC
        return (v, e)
  _ <- sstring "let"
  bs <- RP.sepBy pDef (schar ';')
  _ <- sstring "in"
  e <- rpLC
  return $ foldr lcLet e bs
-}

schar :: Char -> ReadP Char
schar c = do RP.skipSpaces; RP.char c

sstring :: String -> ReadP String
sstring c = do RP.skipSpaces; RP.string c

pVar :: (Read v) => ReadP v
pVar = do RP.skipSpaces; RP.readS_to_P (readsPrec 9)

instance (BindingImpl v) => Show (LC v) where
  show = PP.renderStyle PP.style . ppLC 0

ppLC :: forall v. (BindingImpl v) => Int -> LC v -> Doc
ppLC _ (Var v) = PP.text $ show v
ppLC p (Lam b) = pparens (p > 0) $ PP.text ("\\" ++ show v ++ ".") PP.<> ppLC 0 e
  where
    (v, e) = runBindM @v (unbind @v b)
ppLC p (App f a) = pparens (p > 1) $ ppLC 1 f PP.<+> ppLC 2 a

pparens :: Bool -> Doc -> Doc
pparens True d = PP.parens d
pparens False d = d

---------------- Arbitrary ------------------------------------------
lam' :: forall v. BindingImpl v => v -> LC v -> LC v
lam' v e = runBindM @v (Lam <$> bind v e)

bind' :: forall v. (BindingImpl v) => v -> LC v -> Bind v
bind' v a = runBindM @v (bind v a)

unbind' :: forall v. (BindingImpl v) => Bind v -> (v, LC v)
unbind' b = runBindM @v (unbind b)

instance BindingImpl v => Arbitrary (LC v) where
  arbitrary = sized gen
    where
      gen n
        | n <= 1 = Var <$> (arbitrary :: Gen v)
        | otherwise =
          frequency
            [ (1, Var <$> arbitrary),
              (1, Lam <$> (bind' @v <$> arbitrary <*> gen (n `div` 2))),
              (1, App <$> gen (n `div` 2) <*> gen (n `div` 2))
            ]

  shrink (Var v) = [Var n | n <- shrink v]
  shrink (Lam b) =
    e :
    [Lam (bind' n e) | n <- shrink v]
      ++ [Lam (bind' v e') | e' <- shrink e]
    where
      (v, e) = unbind' b
  shrink (App e1 e2) =
    [App e1' e1 | e1' <- shrink e1]
      ++ [App e1 e2' | e2' <- shrink e2]

-- | Generate an arbitrary *well-scoped* lambda calculus term
-- biased in terms of the lam constructor
genScoped :: forall v. (Enum v, BindingImpl v) => Gen (LC v)
genScoped = lams <$> sized (gen vars)
  where
    vars :: [v]
    vars = take 5 [(toEnum 0) ..]

    lams :: LC v -> LC v
    lams body = foldr lam' body vars

    gen :: [v] -> Int -> Gen (LC v)
    gen xs n
      | not (null xs) && n <= 1 = var
      | null xs = oneof [lam, app]
      | otherwise = oneof [var, lam, lam, lam, app]
      where
        n' = n `div` 2
        lam = do
          let x = succ (head xs)
          Lam <$> (bind' x <$> gen (x : xs) n')
        app = App <$> gen xs n' <*> gen xs n'
        var = Var <$> elements xs

-- | Shrink an arbitrary *well-scoped* lambda calculus term
shrinkScoped :: forall v. (Enum v, BindingImpl v) => LC v -> [LC v]
shrinkScoped e = lams <$> s (peel e)
  where
    vars = take 5 [(toEnum 0) ..]

    lams :: BindingImpl v => LC v -> LC v
    lams body = foldr (\v e -> Lam (bind' v e)) body vars

    peel :: LC v -> LC v
    peel (Lam b1)
      | (_, Lam b2) <- unbind' @v b1,
        (_, Lam b3) <- unbind' @v b2,
        (_, Lam b4) <- unbind' @v b3,
        (_, Lam b5) <- unbind' @v b4,
        (_, e1) <- unbind' b5 =
        e1
    peel _ = error "start with 5 lambda-bound variables"

    s :: BindingImpl v => LC v -> [LC v]
    s (Lam b) = [e] where (v, e) = unbind' b
    s (Var _x) = []
    s (App e1 e2) = e1 : e2 : [App e1 e2' | e2' <- s e2] ++ [App e1' e2 | e1' <- s e1]

----------------------------------------------------------------
