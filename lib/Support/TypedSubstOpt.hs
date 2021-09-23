{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Binding library for locally nameless representation
module Support.TypedSubstOpt
  ( VarC (..),
    AlphaC (..),
    SubstC (..),
    Var (..),
    isBound,
    isFree,
    prettyVar,
    multiSubstBvVar,
    multiSubstFvVar,
    substFvVar,
    -- substBvVar,
    Bind,
    bind,
    unbind,
    instantiate,
    open,
    close,
    substFv,
  )
where

import qualified Control.Monad.State as State
import Data.List (elemIndex)
import Data.Type.Equality hiding (apply)
import Debug.Trace
import GHC.Stack
import qualified Unsafe.Coerce as Unsafe
import Util.IdInt (IdInt (..), firstBoundId)
import qualified Util.IdInt.Map as M
import qualified Util.IdInt.Set as S
import Util.Impl (LambdaImpl (..))
import Util.Imports hiding (S, from, to)
import qualified Util.Syntax.Lambda as LC
import Util.Nat

-------------------------------------------------------------------

-- | Type class of syntactic forms that contain variable constructors
class VarC (a :: Nat -> Type) where
  var :: Var n -> a n

  isvar :: a n -> Maybe (Var n)
  isvar _ = Nothing
  {-# INLINE isvar #-}

-- | Type for syntactic forms
class AlphaC (a :: Nat -> Type) where
  -- | calculate the free variables of a term
  fv :: a n -> S.IdIntSet

  -- | replace bound variables (starting at k) with a list of free variables (i.e. [IdInt])
  -- NOTE: the term we are replacing into may not be locally closed
  multi_open_rec :: Sub IdInt n k -> a (Plus n k) -> a k

  -- | replace free variables (noted as "IdInt") with their respective bound variables
  -- starting at index k
  multi_close_rec :: SNat k -> Vec IdInt n -> a k -> a (Plus n k)

-- | Type class for substitution functions
class AlphaC a => SubstC b a where
  -- | substitute for multiple free variables
  multi_subst_fv :: M.IdIntMap b -> a n -> a n

  -- | substitute for multiple bound variables (starting at index k)
  multi_subst_bv :: forall n k. Sub b n k -> a (Plus n k) -> a k

--------------------------------------------------------------

-- We can always move syntax into a larger scope

weaken :: forall n k a. a k -> a (Plus n k)
weaken = Unsafe.unsafeCoerce

--------------------------------------------------------------

data Vec a (n :: Nat) where
  VNil :: Vec a 'Z
  VCons :: !a -> !(Vec a n) -> Vec a ('S n)

instance Show a => Show (Vec a n) where
  show VNil = ""
  show (VCons x VNil) = show x
  show (VCons x xs) = show x ++ "," ++ show xs

-- deriving instance Show a => (Show (Vec a n))

inth :: Idx n -> Vec a n -> a
inth FZ (VCons a _) = a
inth (FS m) (VCons _ ss) = inth m ss

append :: Vec a m -> Vec a n -> Vec a (Plus m n)
append VNil v = v
append (VCons u vm) vn = VCons u (append vm vn)

--------------------------------------------------------------
-- Index manipulation for multi_close

find :: IdInt -> Vec IdInt n -> Maybe (Idx n)
find _x VNil = Nothing
find x (VCons y vs)
  | x == y = Just FZ
  | otherwise = FS <$> find x vs

-- add k to the appropriate index
-- this actually changes the index values.
shiftIdx :: forall n k. SNat k -> Idx n -> Idx (Plus n k)
shiftIdx SZ n
  | Refl <- plus_Z_r @n = n
shiftIdx (SS (k0 :: SNat k0)) n
  | Refl <- plus_S_r @n @k0 = FS (shiftIdx k0 n)
{-# INLINE shiftIdx #-}

plus_Z_r :: forall n. Plus n 'Z :~: n
plus_Z_r = Unsafe.unsafeCoerce Refl
{-# INLINE plus_Z_r #-}

plus_S_r :: forall n k. 'S (Plus n k) :~: Plus n ('S k)
plus_S_r = Unsafe.unsafeCoerce Refl
{-# INLINE plus_S_r #-}

--------------------------------------------------------------
-- Index manipulation for multi_openc
-- return the nth element of the list, or some default

--------------------------------------------------------------

-- A vector of length n, starting at position k
-- mapping to idints or locally-closed terms
data Sub a n k where
  Sub :: !(SNat k) -> !(Vec a n) -> Sub a n k

instance Show a => Show (Sub a n k) where
  show (Sub n vs) = show n ++ "|->" ++ show vs

--------------------------------------------------------------

-- | Variables, bound and free
data Var n = B !(Idx n) | F {-# UNPACK #-} !IdInt deriving (Generic, Eq, Show)

isBound :: Var n -> Bool
isBound (B _) = True
isBound (F _) = False

isFree :: Var n -> Bool
isFree (B _) = False
isFree (F _) = True

-- | Display the variable without the outermost constructor
prettyVar :: Var n -> String
prettyVar (B i) = "b" ++ show i
prettyVar (F x) = show x

instance NFData (Var n)

instance AlphaC Var where
  fv (B _) = S.empty
  fv (F x) = S.singleton x
  {-# INLINE fv #-}

  multi_close_rec ::
    forall n k.
    SNat k ->
    Vec IdInt n ->
    Var k ->
    Var (Plus n k)
  multi_close_rec k xs (F x) =
    case find x xs of
      Just n -> (B (shiftIdx k n))
      Nothing -> (F x)
  multi_close_rec _k _xs (B n2) =
    (B (weaken @n n2))
  {-# INLINE multi_close_rec #-}

  multi_open_rec :: forall n k. Sub IdInt n k -> Var (Plus n k) -> Var k
  multi_open_rec _s (F x) = F x
  multi_open_rec (Sub k vn) (B i) =
    case substIdx i k vn of
      Left x -> F x
      Right j -> B j
  {-# INLINE multi_open_rec #-}

-- If index i is  <= k then select from vector
-- otherwise decrease index to k
substIdx ::
  forall n k b.
  Idx (Plus n k) ->
  SNat k ->
  Vec b n ->
  Either b (Idx k)
substIdx FZ SZ (VCons i _) = Left $ i
substIdx (FS f) SZ (VCons _ vs) = substIdx f SZ vs
substIdx FZ (SS _) _vs
  | Refl <- plus_S_r @n @k = Right $ FZ
-- subtract k from i
substIdx (FS f) (SS (l :: SNat l)) vs
  | Refl <- plus_S_r @n @l =
    case substIdx @n @l f l vs of
      Left i -> Left i
      Right i -> Right (FS i)

-- We need this instance for the generic version
-- but we should *never* use it
-- NB: may make sense to include overlapping instances?
-- b/c the SubstC Var Var instance does make sense.
instance SubstC b Var where
  multi_subst_fv _ _ = error "BUG: should not reach here"
  multi_subst_bv _k _ = error "BUG: should not reach here"
  {-# INLINE multi_subst_bv #-}

-- | multi substitution for a single bound variable
-- starts at index k leaves all other variables alone
multiSubstBvVar :: forall k n a. (VarC a) => Sub (a 'Z) n k -> Var (Plus n k) -> a k
multiSubstBvVar (Sub k vs) (B i)
  | Refl <- plus_Z_r @k =
    case substIdx i k vs of
      Left x -> weaken @k x
      Right j -> var (B j)
multiSubstBvVar _ (F x) = var (F x)
{-# INLINEABLE multiSubstBvVar #-}

-- | multi substitution for a single free variable
multiSubstFvVar :: forall n a. VarC a => M.IdIntMap (a 'Z) -> Var n -> a n
multiSubstFvVar m v@(F x)
  | Refl <- plus_Z_r @n =
    case m M.!? x of
      Just y -> weaken @n y
      Nothing -> var v
multiSubstFvVar _ v@(B _) = var v

-- | single substitution for a single free variable
substFvVar :: forall n a. VarC a => a 'Z -> IdInt -> Var n -> a n
substFvVar u y (F x) | x == y, Refl <- plus_Z_r @n = weaken @n u
substFvVar _ _ v = var v
{-# INLINEABLE substFvVar #-}

-------------------------------------------------------------------

-- Caching open/close at binders.
-- To speed up this implementation, we delay the execution of subst_bv / open / close
-- in a binder so that multiple traversals can fuse together

data Bind a k where
  Bind :: BindInfoList a ('S m) ('S n) -> !(a ('S m)) -> Bind a n

data BindInfoList a m n where
  None :: BindInfoList a n n
  Cons :: !(BindInfo a m k) -> !(BindInfoList a n m) -> BindInfoList a n k

data BindInfo a n k where
  SubstBv :: !(Sub (a 'Z) n k) -> BindInfo a (Plus n k) k
  SubstFv :: !(M.IdIntMap (a 'Z)) -> BindInfo a k k
  Open :: !(Sub IdInt n k) -> BindInfo a (Plus n k) k
  Close :: !(SNat k) -> !(Vec IdInt n) -> BindInfo a k (Plus n k)

deriving instance (Show (a 'Z)) => Show (BindInfo a n k)

instance (Show (a 'Z)) => Show (BindInfoList a m n) where
  show None = ""
  show (Cons x None) = show x
  show (Cons x xs) = show x ++ "," ++ show xs

deriving instance (forall m. Show (a m)) => Show (Bind a k)

instance (Eq (a ('S n)), SubstC (a 'Z) a) => Eq (Bind a n) where
  b1 == b2 = unbind b1 == unbind b2

-- TODO: fix this!
instance (forall m. NFData (a m), SubstC (a 'Z) a) => NFData (Bind a n) where
  rnf b = rnf (unbind b)

-- | create a binding by "abstracting a variable"
bind :: AlphaC a => a ('S k) -> Bind a k
bind a = Bind None a
{-# INLINEABLE bind #-}

apply :: forall m k a. SubstC (a 'Z) a => BindInfo a m k -> a m -> a k
apply (SubstBv ss) = multi_subst_bv ss
apply (SubstFv m) = multi_subst_fv m
apply (Close k vs) = multi_close_rec k vs
apply (Open ss) = multi_open_rec ss
{-# INLINE apply #-}

-- Compress and apply the delayed operations in the body of the term
applyAll :: (SubstC (a 'Z) a) => BindInfoList a n k -> a n -> a k
applyAll None = id
applyAll (Cons bi bis) = apply bi . applyAll bis

unbind :: (SubstC (a 'Z) a) => Bind a k -> a ('S k)
unbind (Bind bis a) = applyAll bis a
{-# INLINEABLE unbind #-}

-- addBindInfo :: (SubstC (a 'Z) a) => BindInfo a -> Bind a k -> Bind a k
-- addBindInfo bi (Bind bis0 a) = Bind (add bi bis0) a
{-  where
    {-    add x@(Open k vn) y@(Open l vm : bis)
          | l - k == length vn =
                 trace (" Open^ k=" ++ show k ++ " vn=" ++ show vn ++ " l=" ++ show l ++ " vm=" ++ show vm) $
                   add (Open l (vn <> vm)) bis -}
    add (Close _k xs) (Close k0 ys : bis) =
      add (Close k0 (ys <> xs)) bis
    add (SubstBv k vn) (SubstBv l vm : bis)
      | l - k == length vn =
        add (SubstBv k (vn <> vm)) bis
      | otherwise =
        trace ("VIOLATION k=" ++ show k ++ " |vn|=" ++ show (length vn) ++ " l=" ++ show l) $
          add (SubstBv k (vn <> vm)) bis
    -- add (SubstFv m1) (SubstFv m2 : bis) = trace "subst" $ add (SubstFv (m1 `comp` m2)) bis
    add (SubstFv m1) (Open k vm : bis)
      | fm `isDom` m1 = add (SubstBv k (map (m1 M.!) fm)) bis
      where
        fm = freeVars vm
    add x bis = (x : bis)
{-# INLINEABLE addBindInfo #-}
-}

plus_assoc :: forall m n p. Plus (Plus m n) p :~: Plus m (Plus n p)
plus_assoc = Unsafe.unsafeCoerce Refl

plus_comm :: forall m n. Plus m n :~: Plus n m
plus_comm = Unsafe.unsafeCoerce Refl

instance (SubstC (a 'Z) a) => AlphaC (Bind a) where
  fv b = fv (unbind b)
  {-# INLINE fv #-}

  multi_open_rec :: forall n k. Sub IdInt n k -> Bind a (Plus n k) -> Bind a k
  {- multi_open_rec
    (Sub k vn)
    (Bind (Cons (Open (Sub l vm)) (bis :: BindInfoList a ('S m) m1)) (b :: a ('S m)))
      | Refl <- plus_S_r @n @k =
        Bind (Cons bi (bis :: _)) b
      where
        bi :: _ -- BindInfo a (Plus n ('S k)) ('S k)
        bi = undefined -}
  multi_open_rec (Sub k vn) (Bind bis b)
    | Refl <- plus_S_r @n @k =
      Bind (Cons bi bis) b
    where
      bi :: BindInfo a (Plus n ('S k)) ('S k)
      bi = Open (Sub (SS k) vn)
  {-# INLINE multi_open_rec #-}

  multi_close_rec ::
    forall n k.
    SNat k ->
    Vec IdInt n ->
    Bind a k ->
    Bind a (Plus n k)
  multi_close_rec
    (_k :: SNat k)
    xs
    ( Bind
        ( Cons
            (Close (m :: SNat m1) (ys :: Vec IdInt n1))
            (bis :: BindInfoList a ('S m) m1)
          )
        (b :: a ('S m))
      )
      | Refl <- plus_S_r @n @k,
        Refl <- plus_comm @n1 @n,
        Refl <- plus_assoc @n @n1 @m1 =
        Bind (Cons (Close m (append ys xs)) bis) b
  multi_close_rec k xs (Bind bis b)
    | Refl <- plus_S_r @n @k =
      Bind
        (Cons (Close (SS k) xs) bis)
        b
  {-# INLINE multi_close_rec #-}

instance (SubstC (a 'Z) a) => SubstC (a 'Z) (Bind a) where
  multi_subst_bv :: forall n k. Sub (a 'Z) n k -> Bind a (Plus n k) -> Bind a k
  multi_subst_bv (Sub k vn) (Bind bis b)
    | Refl <- plus_S_r @n @k =
      Bind (Cons bi bis) b
    where
      bi :: BindInfo a (Plus n ('S k)) ('S k)
      bi = SubstBv (Sub (SS k) vn)
  {-# INLINE multi_subst_bv #-}

  multi_subst_fv :: M.IdIntMap (a 'Z) -> Bind a n -> Bind a n
  multi_subst_fv m1 (Bind bis b) =
    Bind (Cons (SubstFv m1) bis) b
  {-# INLINE multi_subst_fv #-}

isDom :: [IdInt] -> M.IdIntMap a -> Bool
isDom fm m = S.fromList fm == M.keysSet m

substSub :: (Functor f, SubstC (a 'Z) a) => M.IdIntMap (a 'Z) -> f (a k) -> f (a k)
substSub s2 s1 = fmap (multi_subst_fv s2) s1
{-# INLINEABLE substSub #-}

comp :: SubstC (a 'Z) a => M.IdIntMap (a 'Z) -> M.IdIntMap (a 'Z) -> M.IdIntMap (a 'Z)
comp s1 s2
  | M.null s1 = s2
  | M.null s2 = s1
  -- union is left biased. We want the value from s2 if there is also a definition in s1
  -- but we also want the range of s2 to be substituted by s1
  | otherwise = substSub s1 s2 <> s1
{-# INLINEABLE comp #-}

-----------------------------------------------------------------

open :: (Show (a 'Z), SubstC (a 'Z) a) => Bind a 'Z -> IdInt -> a 'Z
open (Bind (Cons (Open (Sub (SS SZ) (vs :: Vec IdInt n))) bis) b) u
  | Refl <- plus_S_r @n @'Z =
    multi_open_rec (Sub SZ (VCons u vs)) (unbind (Bind bis b))
open b x = result
  where
    result = multi_open_rec (Sub SZ (VCons x VNil)) (unbind b)
{-# INLINEABLE open #-}

close :: (AlphaC a, Show (a ('S 'Z))) => IdInt -> a 'Z -> Bind a 'Z
close x e = bind result
  where
    result = (multi_close_rec SZ (VCons x VNil) e)
{-# INLINEABLE close #-}

-- | Note: in this case, the binding should be locally closed
instantiate :: (Show (a 'Z), SubstC (a 'Z) a) => Bind a 'Z -> a 'Z -> a 'Z
instantiate (Bind (Cons (SubstBv (Sub (SS SZ) (vs :: Vec (a 'Z) n))) bis) b) u
  | Refl <- plus_S_r @n @'Z =
    multi_subst_bv (Sub SZ (VCons u vs)) (unbind (Bind bis b))
instantiate b u = result
  where
    result = multi_subst_bv (Sub SZ (VCons u VNil)) (unbind b)
{-# INLINEABLE instantiate #-}

substFv :: (SubstC b a) => b -> IdInt -> a k -> a k
substFv b x a =
  result
  where
    result = multi_subst_fv (M.singleton x b) a
{-# INLINEABLE substFv #-}

---------------------------------------------------------------------

----------------------------------------------------------------
