> module Misc(stripComments, interactArgs) where
> import System(getArgs)

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

