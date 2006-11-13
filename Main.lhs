> import Misc
> import Lambda
> import IdInt
> import Simple
> import Unique
> import HOAS
> import DeBruijn
> import DeBruijnC

> main :: IO ()
> main = interactArgs $
>         \ args -> (++ "\n") . show . myNF args . toIdInt . f . read . stripComments
>   where f :: LC Id -> LC Id  -- just to force the type
>         f e = e
>         myNF ["U"] = Unique.nf
>         myNF ["H"] = HOAS.nf
>         myNF ["D"] = DeBruijn.nf
>         myNF ["C"] = DeBruijnC.nf
>         myNF ["S"] = Simple.nf

Timing in seconds on a MacBook processing the file {\tt timing.lam}.

\begin{center}
\begin{tabular}{|l|r@{.}l|}
\hline
Simple.nf	& 8&3  \\
Unique.nf	& 26&6 \\
HOAS.nf		& 0&13 \\
DeBruijn.nf     & 41&1 \\
DeBruijnEnv.nf  & 41&1 \\
\hline
\end{tabular}
\end{center}

The $\lambda$-expression in {\tt timing.lam} computes
``{\tt factorial 6 == sum [1..37] + 17}'', but using Church numerals.

\mbox{}\\
\mbox{}\\
{\tt timing.lam:}
\begin{verbatim}
let False = \f.\t.f;
    True = \f.\t.t;
    if = \b.\t.\f.b f t;
    Zero = \z.\s.z;
    Succ = \n.\z.\s.s n;
    one = Succ Zero;
    two = Succ one;
    three = Succ two;
    isZero = \n.n True (\m.False);
    const = \x.\y.x;
    Pair = \a.\b.\p.p a b;
    fst = \ab.ab (\a.\b.a);
    snd = \ab.ab (\a.\b.b);
    fix = \ g. (\ x. g (x x)) (\ x. g (x x));
    add = fix (\radd.\x.\y. x y (\ n. Succ (radd n y)));
    mul = fix (\rmul.\x.\y. x Zero (\ n. add y (rmul n y)));
    fac = fix (\rfac.\x. x one (\ n. mul x (rfac n)));
    eqnat = fix (\reqnat.\x.\y. x (y True (const False)) (\x1.y False (\y1.reqnat x1 y1)));
    sumto = fix (\rsumto.\x. x Zero (\n.add x (rsumto n)));
    n5 = add two three;
    n6 = add three three;
    n17 = add n6 (add n6 n5);
    n37 = Succ (mul n6 n6);
    n703 = sumto n37;
    n720 = fac n6
in  eqnat n720 (add n703 n17)
\end{verbatim}

\section{Conclusions}
This test is too small to draw any deep conclusions, but higher order
syntax looks very good.  Furthermore, doing the simplest thing is not
necessarily bad.

