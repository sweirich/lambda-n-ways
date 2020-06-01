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
> import SimpleB
> import Unique
> import HOAS
> import DeBruijn
> import DeBruijnC
> import DeBruijnParF
> import DeBruijnParB
> import BoundDB
> import Unbound
> import DeBruijnScoped
> import Test.QuickCheck
> -- import Core.Nf
>
> import Criterion.Main
> import Control.DeepSeq
>

Every lambda calculus implementation must have 
a way to convret to and from the "raw string" representation, 
a way to compute the normal form, and a way to determine
alpha-equivalence.


> data LamImpl =
>   forall a. NFData a =>
>       LamImpl
>          { impl_name   :: String ,
>            impl_fromLC :: LC IdInt -> a ,
>            impl_toLC   :: a -> LC IdInt,
>            impl_nf     :: a -> a,
>            impl_aeq    :: a -> a -> Bool,
>            impl_nfi    :: Int -> a -> Maybe a
>          }
 


> data Bench =
>   forall a. Bench String (a -> ()) a


> impls :: [LamImpl]
> impls = [ 
>           LamImpl "DB_B" DeBruijnParB.toDB DeBruijnParB.fromDB DeBruijnParB.nfd (==)
>                          DeBruijnParB.nfi
>         , LamImpl "Scoped" DeBruijnScoped.toDB DeBruijnScoped.fromDB DeBruijnScoped.nfd (==)
>                          DeBruijnScoped.nfi
>         , LamImpl "DB_C" (DeBruijnC.fromLC []) (DeBruijnC.toLC 0) DeBruijnC.nfd (==)
>                          (\x y -> Nothing)
>         , LamImpl "Bound" BoundDB.toDB BoundDB.fromDB BoundDB.nfd
>                          (==) (\x y -> Nothing)
>         , LamImpl "HOAS"   HOAS.fromLC HOAS.toLC HOAS.nfh 
>            (\x y -> Lambda.aeq (HOAS.toLC x) (HOAS.toLC y))
>                          (\x y -> Nothing)
>         , LamImpl "DB_F" DeBruijnParF.toDB DeBruijnParF.fromDB DeBruijnParF.nfd
>                          (==) DeBruijnParF.nfi
> --        , LamImpl "DB_P" DeBruijnPar.toDB DeBruijnPar.fromDB DeBruijnPar.nfd
> --                         (==)
>         , LamImpl "SimpleB" SimpleB.toExp SimpleB.fromExp SimpleB.nfd SimpleB.aeqd
>                            SimpleB.nfi
> {-        , LamImpl "Simple" id id Simple.nf Lambda.aeq Simple.nfi
>         , LamImpl "DB" DeBruijn.toDB DeBruijn.fromDB DeBruijn.nfd (==) DeBruijn.nfi
>         , LamImpl "Unbound" Unbound.toDB Unbound.fromDB Unbound.nfu
>                          Unbound.aeqd (\x y -> Nothing)
>         , LamImpl "Unique" id id Unique.nf Unique.aeq (\x y -> Nothing)
> --      , LamImpl "Core" id id Core.Nf.nf Lambda.aeq -}
>         ]

> nf_bs :: LC IdInt -> [Bench]
> nf_bs lc = map impl2nf impls where
>   impl2nf LamImpl {..} =
>     let! tm = force (impl_fromLC lc) in
>     Bench impl_name (rnf . impl_nf) tm

> aeq_bs :: LC IdInt -> LC IdInt -> [Bench]
> aeq_bs lc1 lc2 = map impl2aeq impls where
>   impl2aeq LamImpl {..} =
>     let! tm1 = force (impl_fromLC lc1) in
>     let! tm2 = force (impl_fromLC lc2) in
>     Bench impl_name (\(x,y) -> rnf (impl_aeq x y)) (tm1,tm2)


> getTerm :: IO (LC Id)
> getTerm = do
>   contents <- readFile "timing.lam"
>   return $ read (stripComments contents)


> prop_rt :: LamImpl -> LC IdInt -> Bool
> prop_rt LamImpl{..} x = impl_toLC (impl_fromLC x) `Lambda.aeq` x

> prop_aeq :: Property
> prop_aeq = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
>    forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \y ->
>        let eq = Lambda.aeq x y in
>        classify eq "aeq" $ eq == (DeBruijn.toDB x == DeBruijn.toDB y)


> eqMaybe :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Property
> eqMaybe f (Just x) (Just y) = classify True "aeq" (f x y)
> eqMaybe _f Nothing Nothing = property True
> eqMaybe _ _ _ = property False

> prop_sameNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Int -> LC IdInt ->  Property
> prop_sameNF f i x = eqMaybe Lambda.aeq (Simple.nfi i x) (f i x)

> -- NOTE: need "fueled" version of normalization 
> -- NOTE: hard to shrink and stay well-closed
> prop_closedNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Property
> prop_closedNF f = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
>       eqMaybe Unique.aeq (DeBruijn.fromDB <$> DeBruijn.nfi 1000 (DeBruijn.toDB x)) (f 1000 x)


> prop_unique :: LC IdInt -> Bool
> prop_unique x = Unique.aeq x (Unique.toUnique x)

> infixl 5 @@
> a @@ b  = App a b
> lam i b = Lam (IdInt i) b
> var i   = Var (IdInt i)

-- test case that demonstrates the issue with renaming with a bound variable
-- the simplifications to t2 and t3 below do not demonstrate the bug, only t1
-- note how x3 is already in scope, 


> t1 :: LC IdInt
> t1 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>         (  (lam 1 (lam 2 (lam 3 ( var 1 @@ (lam 4 (var 4)))))) @@
>            (  (lam 1 (lam 2 ((lam 3 (var 2)) @@ (var 1 @@ var 3)))) @@
>               (lam 1 (lam 2 (var 3)))))))))


\x0.\x1.\x2.\x3.\x4.(\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.(\x3.x2) (x1 x3)) (\x1.\x2.x3))

\x0.\x1.\x2.\x3.\x4.
    (\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.(\x3.x2) (x1 x3)) (\x1.\x2.x3))
-->
    (\x1.\x2.\x3.x1 (\x4.x4)) ((\x1.\x2.x2) (\x1.\x2.x3))

> t2 :: LC IdInt
> t2 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>         (  (lam 1 (lam 2 (lam 3 ( var 1 @@ (lam 4 (var 4)))))) @@
>            (  (lam 1 (lam 2 (var 2))) @@
>               (lam 1 (lam 2 (var 3)))))))))


\x0.\x1.\x2.\x3.\x4.\x1.\x2.(\x3.x2) (x1 x3)


> t3 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>          (lam 1 (lam 2 ((lam 3 (var 2)) @@ (var 1 @@ var 3))))))))

\x0.\x1.\x2.\x3.\x4.
   (\x1.x1 ((\x2.x1) (\x2.x2) (\x2.x2 x1))) (\x1.\x2.(\x3.\x4.x1) (\x3.x3 x2))

> t4 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4
>        ((lam 1 (var 1 @@ ((lam 2 (var 1)) @@ (lam 2 (var 2)) @@ (lam 2 (var 2 @@ var 1)))))
>        @@
>        (lam 1 (lam 2 ( (lam 3 (lam 4 (var 1))) @@ (lam 3 (var 3 @@ var 2))))))))))




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
