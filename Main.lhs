> import Lambda
> import IdInt
> import Simple
> import Unique
> import HOAS

> main :: IO ()
> main = interact $ (++ "\n") . show . HOAS.nf . toIdInt . f . read . stripComments
>   where f :: LC Id -> LC Id
>         f e = e

Strip away Ada style comments.

> stripComments :: String -> String
> stripComments "" = ""
> stripComments ('-':'-':cs) = skip cs
>   where skip "" = ""
>         skip s@('\n':_) = stripComments s
>         skip (_:s) = skip s
> stripComments (c:cs) = c : stripComments cs

Timing, Sharp PC-MM20 (1GHz Efficeon CPU), for timing.lam
Simple.nf	 38s
Unique.nf	494s
HOAS.nf		  1s
