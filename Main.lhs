> import Misc
> import Lambda
> import IdInt
> import Simple
> import Unique
> import HOAS
> import DeBruijn

> main :: IO ()
> main = interactArgs $
>         \ args -> (++ "\n") . show . myNF args . toIdInt . f . read . stripComments
>   where f :: LC Id -> LC Id  -- just to force the type
>         f e = e
>         myNF ["U"] = Unique.nf
>         myNF ["H"] = HOAS.nf
>         myNF ["D"] = DeBruijn.nf
>         myNF ["S"] = Simple.nf

Strip away Ada style comments.

> stripComments :: String -> String
> stripComments "" = ""
> stripComments ('-':'-':cs) = skip cs
>   where skip "" = ""
>         skip s@('\n':_) = stripComments s
>         skip (_:s) = skip s
> stripComments (c:cs) = c : stripComments cs

Like `interact', but also pass program arguments.

> interactArgs :: ([String] -> String -> String) -> IO ()
> interactArgs f = do
>     args <- getArgs
>     interact (f args)

Timing, Sharp PC-MM20 (1GHz Efficeon CPU), for timing.lam
Simple.nf	 38s
Unique.nf	494s
HOAS.nf		  1s

       29
      212
        0.4

-O2
       16
       94
        0.27
       24
