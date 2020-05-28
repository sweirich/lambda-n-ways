> {-# LANGUAGE ExistentialQuantification #-}
> {-# LANGUAGE BangPatterns #-}
> {-# LANGUAGE RecordWildCards #-}
> 
> module Main where
> 
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
>
>
> data LamImpl =
>   forall a. NFData a =>
>       LamImpl
>          { impl_name   :: String ,
>            impl_fromLC :: LC IdInt -> a ,
>            impl_toLC   :: a -> LC IdInt,
>            impl_nf :: a -> a,
>            impl_aeq    :: Maybe (a -> a -> Bool)
>          }
>
> data Bench =
>   forall a. Bench String (a -> ()) a
> 
> impls :: [LamImpl]
> impls = [ LamImpl "Simple" id id Simple.nf (Just Simple.aeq)
>         , LamImpl "Unique" id id Unique.nf (Just Unique.aeq)
>         , LamImpl "HOAS"   HOAS.fromLC HOAS.toLC HOAS.nfh Nothing
>         , LamImpl "DB" DeBruijn.toDB DeBruijn.fromDB DeBruijn.nfd (Just (==))
>         , LamImpl "DB_C" (DeBruijnC.fromLC [])
>                          (DeBruijnC.toLC 0)
>                           DeBruijnC.nfd (Just (==))
>         , LamImpl "DB_P" DeBruijnPar.toDB DeBruijnPar.fromDB DeBruijnPar.nfd
>                          (Just (==))
>         , LamImpl "DB_B" DeBruijnParB.toDB DeBruijnParB.fromDB DeBruijnParB.nfd
>                          (Just (==))
>         , LamImpl "Bound" BoundDB.toDB BoundDB.fromDB BoundDB.nfd
>                          (Just (==))
> --        , LamImpl "Unbound" Unbound.toDB Unbound.fromDB Unbound.nfu
> --                         (Just Unbound.aeqd)
>         , LamImpl "Scoped"
>                          DeBruijnScoped.toDB DeBruijnScoped.fromDB DeBruijnScoped.nfd
>                          (Just (==))
>         ]

> nf_bs :: LC IdInt -> [Bench]
> nf_bs lc = map impl2nf impls where
>   impl2nf (LamImpl {..}) =
>     let! tm = force (impl_fromLC lc) in
>     Bench impl_name (rnf . impl_nf) tm

> aeq_bs :: LC IdInt -> LC IdInt -> [Bench]
> aeq_bs lc1 lc2 = map impl2nf impls where
>   impl2nf (LamImpl {..}) =
>     let! tm1 = force (impl_fromLC lc1) in
>     let! tm2 = force (impl_fromLC lc2) in
>     let  a   = case impl_aeq of { Just f -> f ; Nothing -> \x y -> True } in
>     Bench impl_name (\(x,y) -> rnf (a x y)) (tm1,tm2)


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
> aeqs = [ ("Simple", Simple.aeq), 
>         ("Unique", Unique.aeq), 
>         -- ("HOAS", HOAS.aeq),  -- No good definition
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
>   let tm1 = toIdInt tm
>   return $! rnf tm1
>   let tm2 = toIdInt (toUnique tm1)
>   return $! rnf tm2
>   let! nfs = nf_bs tm1
>   let! aeqs = aeq_bs tm1 tm2
>   let runBench (Bench n f x) = bench n $ Criterion.Main.nf f x
>   defaultMain [
>      bgroup "nf" $ map runBench nfs
>    , bgroup "aeq" $ map runBench aeqs
>    ]
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

