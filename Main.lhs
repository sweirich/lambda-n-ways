> import Lambda
> import IdInt
> import Simple
> import Unique
> import HOAS

> main :: IO ()
> main = interact $ (++ "\n") . show . Simple.nf . toIdInt . f . read
>   where f :: LC Id -> LC Id
>         f e = e

Timing, Sharp PC-MM20 (1GHz Efficeon CPU), for timing.lam
Simple.nf	38s
