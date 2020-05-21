> import Misc
> import Lambda
> import IdInt
> import Simple
> import Unique
> import HOAS
> import DeBruijn
> import DeBruijnC
> import DeBruijnPar
> import DeBruijnParB
> import BoundDB
> import Unbound
> import DeBruijnScoped
>
> import Criterion.Main
> import Control.DeepSeq

> instance NFData a => NFData (LC a)
> instance NFData IdInt

> nfs :: [(String, LC IdInt -> LC IdInt)]
> nfs = [("Simple", Simple.nf), 
>         ("Unique", Unique.nf), 
>         ("HOAS", HOAS.nf), 
>         ("DB", DeBruijn.nf), 
>         ("DB_C", DeBruijnC.nf), 
>         ("DB_P", DeBruijnPar.nf), 
>         ("DB_B", DeBruijnParB.nf), 
>         ("Bound", BoundDB.nf), 
>         ("Unbound", Unbound.nf), 
>         ("Scoped", DeBruijnScoped.nf)]
>
> aeqs :: [(String, LC IdInt -> LC IdInt -> Bool)]
> aeqs = [ -- ("Simple", Simple.aeq), 
>         ("Unique", Unique.aeq), 
>         ("HOAS", HOAS.aeq), 
>         ("DB", DeBruijn.aeq), 
>         ("DB_C", DeBruijnC.aeq), 
>         ("DB_P", DeBruijnPar.aeq), 
>         ("DB_B", DeBruijnParB.aeq), 
>         ("Bound", BoundDB.aeq), 
>         ("Unbound", Unbound.aeq), 
>         ("Scoped", DeBruijnScoped.aeq)]

> getTerm :: IO (LC Id)
> getTerm = do
>   contents <- readFile "timing.lam"
>   return $ read (stripComments contents)


> main :: IO ()
> main = do
>   tm <- getTerm
>   let myNF g = g (toIdInt tm)
>   defaultMain [
>      bgroup "nf" $ map (\(n,f) -> bench n $ Criterion.Main.nf myNF f) nfs
>      ]
>
> 


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

