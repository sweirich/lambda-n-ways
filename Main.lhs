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

Timing in seconds on a MacBook processing the file {\tt timing.lam}.

\begin{center}
\begin{tabular}{|l|r@{.}l|}
\hline
Simple.nf	& 8&3  \\
Unique.nf	& 26&6 \\
HOAS.nf		& 0&13 \\
DeBruijn.nf     & 41&1 \\
\hline
\end{tabular}
\end{center}

The $\lambda$-expression in {\tt timing.lam} computes
``{\tt factorial 6 == sum [1..37] + 17}'', but using Church numerals.

\section{Conclusions}
This test is too small to draw any deep conclusions, but higher order
syntax looks very good.  Furthermore, doing the simplest thing is not
necessarily bad.

