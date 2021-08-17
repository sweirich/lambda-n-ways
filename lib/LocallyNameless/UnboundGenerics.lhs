> 
> {-# LANGUAGE DeriveGeneric #-}
> {-# OPTIONS_GHC -fcross-module-specialise #-}
>
> module LocallyNameless.UnboundGenerics(impl) where

> import qualified Util.Lambda as LC
> import Util.IdInt
> import qualified Control.DeepSeq as DS
> import GHC.Generics(Generic)
> import Unbound.Generics.LocallyNameless as U
>    ( Name,
>      s2n,
>      name2Integer,
>      FreshM,
>      runFreshM,
>      FreshMT,
>      runFreshMT,
>      Alpha,
>      Bind,
>      aeq,
>      bind,
>      unbind,
>      Subst(subst, isvar),
>      SubstName(SubstName) )
> import Unbound.Generics.PermM as U
> import Util.Impl ( LambdaImpl(..) )
> import qualified Util.Stats as Stats
> import Control.Monad.Trans(lift)


> impl :: LambdaImpl
> impl = LambdaImpl {
>             impl_name   = "LocallyNameless.UnboundGenerics"
>           , impl_fromLC = toDB
>           , impl_toLC   = fromDB
>           , impl_nf     = nf
>           , impl_nfi    = nfiTop
>           , impl_aeq    = aeq
>        }

> data Exp = Var !(U.Name Exp)
>          | Lam !(U.Bind (U.Name Exp) Exp)
>          | App !Exp !Exp
>  deriving (Show, Generic)
>
> instance DS.NFData Exp where

With representation types, the default implementation of Alpha
provides alpha-equivalence, open, close, and free variable calculation.

> instance U.Alpha Exp

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.

> instance U.Subst Exp Exp where
>   isvar (Var x) = Just (U.SubstName x)
>   isvar _       = Nothing

---------------------------------------------------------------

> nf :: Exp -> Exp
> nf = U.runFreshM . nfd

Computing the normal form proceeds as usual.

> nfd :: Exp -> U.FreshM Exp
> nfd e@(Var _) = return e
> nfd (Lam e)   =
>   do (x, e') <- U.unbind e
>      e1 <- nfd e'
>      return $ Lam (U.bind x e1)
> nfd (App f a) = do
>     f' <- whnf f 
>     case f' of
>         Lam b -> do (x, b') <- U.unbind b
>                     nfd (U.subst x a b')
>         _ -> App <$> nfd f' <*> nfd a

Compute the weak head normal form.

> whnf :: Exp -> U.FreshM Exp
> whnf e@(Var _) = return e
> whnf e@(Lam _) = return e
> whnf (App f a) = do
>     f' <- whnf f
>     case f' of
>         Lam b -> do (x, b') <- U.unbind b
>                     whnf (U.subst x a b')
>         _ -> return $ App f' a

---------------------------------------------------------------

> nfiTop :: Int -> Exp -> Stats.M Exp 
> nfiTop x e = runFreshMT (nfi x e) 

> nfi :: Int -> Exp -> FreshMT Stats.M Exp
> nfi 0 _ = lift Stats.done
> nfi _ e@(Var _) = return e
> nfi n (Lam e) =
>   do
>     (x, e') <- U.unbind e
>     e1 <- nfi (n-1) e'
>     return $ Lam (U.bind x e1)
> nfi n (App f a) = do
>   f' <- whnfi (n-1) f
>   case f' of
>     Lam b -> do (x, b') <- U.unbind b
>                 lift Stats.count
>                 nfi (n-1) (U.subst x a b')
>     _ -> App <$> nfi (n-1) f' <*> nfi (n-1) a

--Compute the weak head normal form.

> whnfi :: Int -> Exp -> FreshMT Stats.M Exp
> whnfi 0 _ = lift Stats.done
> whnfi _ e@(Var _) = return e
> whnfi _ e@(Lam _) = return e
> whnfi n (App f a) = do
>   f' <- whnfi (n-1) f
>   case f' of 
>     Lam b -> do
>        lift Stats.count 
>        (x, b') <- U.unbind b
>        whnfi (n-1) (subst x a b')
>     _ -> return $ App f' a


Convert from LC type to DB type (try to do this in linear time??)

> toDB :: LC.LC IdInt -> Exp
> toDB = to
>   where to :: LC.LC IdInt -> Exp
>         to (LC.Var v)   = Var (i2n v)
>         to (LC.Lam x b) = Lam (U.bind (i2n x) (to b))
>         to (LC.App f a) = App (to f)(to a)
>


Convert back from deBruijn to the LC type.

> n2i :: U.Name Exp -> IdInt
> n2i n = IdInt (fromInteger (name2Integer n))
>
> i2n :: IdInt -> U.Name Exp
> i2n (IdInt x) = s2n (show x)

> fromDB :: Exp -> LC.LC IdInt
> fromDB = U.runFreshM . from 
>   where from :: Exp -> U.FreshM (LC.LC IdInt)
>         from (Var n)   = return $ LC.Var (n2i n)
>         from (Lam b)   = do
>             (x,a) <- unbind b
>             LC.Lam (n2i x) <$> from a
>         from (App f a) = LC.App <$> from f <*> from a 



