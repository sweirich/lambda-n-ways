> import Lambda
> import IdInt
> import Simple

> main :: IO ()
> main = interact $ (++ "\n") . show . nf . {-toIdInt . -} f . read
>   where f :: LC Id -> LC Id
>         f e = e

