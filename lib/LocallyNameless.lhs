> module LocallyNameless where

> import IdInt
> import IdInt.Set
> import Impl


> data Bind b = B b
> bind :: (Alpha t) => Name -> t -> Bind t
> bind n t = B (close n t)
> 
> data Name = FVar IdInt | BVar Int

> data Exp = Var Name | Bind Name Exp | App Exp Exp


> open  :: Alpha a => Name -> a -> a
> open = open' 0
> close :: Alpha  => Name -> a -> a
> close = close' 0

> class Alpha a where
>   aeq   :: a -> a -> Bool
>
> class Idx a where
>   open'  :: Int -> Name -> a -> a
>   close' :: Int -> Name -> a -> a

> class Freevars a where
>   fv :: a -> IdIntSet

> class Subst a b where
>  
