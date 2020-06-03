> {-# LANGUAGE ExistentialQuantification #-}
> {-# LANGUAGE BangPatterns #-}
> {-# LANGUAGE RecordWildCards #-}
> 
> module Main where
> 
> import Misc
> import Lambda
> import IdInt
> import Impl

> import Simple
> import SimpleB
> import Unique
> import HOAS
> import DeBruijn
> -- import DeBruijnC
> import DeBruijnParF
> import DeBruijnParB
> import BoundDB
> import Unbound
> import UnboundGenerics
> import DeBruijnScoped
> import Test.QuickCheck
> import Core.Nf
>
> import Control.Monad
> import Criterion.Main
> import Control.DeepSeq

> data Bench =
>   forall a. Bench String (a -> ()) a


> impls :: [LambdaImpl]
> impls = [ DeBruijnParB.impl
>         , DeBruijnScoped.impl
>         , BoundDB.impl
>         , HOAS.impl
>         , SimpleB.impl
>         , DeBruijnParF.impl
>         , Simple.impl 
>         , DeBruijn.impl
>         , UnboundGenerics.impl 
>         , Unbound.impl
>         , Unique.impl
>         , Core.Nf.impl
>         ]



> -- test the correctness against the DeBruijn implementation
> correctness :: IO ()
> correctness = do
>   tm <- getTerm
>   let tm1 = toIdInt tm
>   let test_impl LambdaImpl{..} = do
>         let result = (impl_toLC . impl_nf . impl_fromLC ) tm1 
>         if Lambda.aeq lambda_false result then return ()
>           else putStrLn $ "FAILED: " ++ impl_name ++ " returned " ++ show result
>   forM_ impls test_impl


> -- | Benchmarks for timing conversion from named representation to internal representation
> conv_bs :: LC IdInt -> [Bench]
> conv_bs lc = map impl2nf impls where
>   impl2nf LambdaImpl {..} =
>     Bench impl_name (rnf . impl_fromLC) lc


> -- | Benchmarks for timing normal form calculation
> nf_bs :: LC IdInt -> [Bench]
> nf_bs lc = map impl2nf impls where
>   impl2nf LambdaImpl {..} =
>     let! tm = force (impl_fromLC lc) in
>     Bench impl_name (rnf . impl_nf) tm

> aeq_bs :: LC IdInt -> LC IdInt -> [Bench]
> aeq_bs lc1 lc2 = map impl2aeq impls where
>   impl2aeq LambdaImpl {..} =
>     let! tm1 = force (impl_fromLC lc1) in
>     let! tm2 = force (impl_fromLC lc2) in
>     Bench impl_name (\(x,y) -> rnf (impl_aeq x y)) (tm1,tm2)


> getTerm :: IO (LC Id)
> getTerm = do
>   contents <- readFile "timing.lam"
>   return $ read (stripComments contents)


> prop_rt :: LambdaImpl -> LC IdInt -> Bool
> prop_rt LambdaImpl{..} x = impl_toLC (impl_fromLC x) `Lambda.aeq` x

> prop_aeq :: Property
> prop_aeq = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
>    forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \y ->
>        let eq = Lambda.aeq x y in
>        classify eq "aeq" $ eq == (DeBruijn.toDB x == DeBruijn.toDB y)


> eqMaybe :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Property
> eqMaybe f (Just x) (Just y) = classify True "aeq" (f x y)
> eqMaybe _f _ _ = property True


> prop_sameNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Int -> LC IdInt ->  Property
> prop_sameNF f i x = eqMaybe Lambda.aeq (Simple.nfi i x) (f i x)

> -- NOTE: need "fueled" version of normalization 
> -- NOTE: hard to shrink and stay well-closed
> prop_closedNF :: (Int -> LC IdInt -> Maybe (LC IdInt)) -> Property
> prop_closedNF f = forAllShrink IdInt.genScoped IdInt.shrinkScoped $ \x ->
>       eqMaybe Unique.aeq (DeBruijn.fromDB <$> DeBruijn.nfi 1000 (DeBruijn.toDB x)) (f 1000 x)

> infixl 5 @@
> (@@) :: LC IdInt -> LC IdInt -> LC IdInt
> a @@ b  = App a b
> lam :: Int -> LC IdInt -> LC IdInt
> lam i b = Lam (IdInt i) b
> var :: Int -> LC IdInt
> var i   = Var (IdInt i)
>
> lambda_false :: LC IdInt
> lambda_false = lam 0 (lam 1 (var 1))

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

-- Counterexample for Core

> t5 :: LC IdInt
> t5 = lam 0 (lam 1 (lam 2 (lam 3 (lam 4 (lam 1 (lam 2 (lam 3 (lam 4 (lam 5 (var 1 @@ var 3))))))))))


> main :: IO ()
> main = do
>   tm <- getTerm
>   let tm1 = toIdInt tm
>   return $! rnf tm1
>   let tm2 = toIdInt (fromUnique (toUnique tm1))
>   return $! rnf tm2
>   let! convs = conv_bs tm1
>   let! nfs = nf_bs tm1
>   let! aeqs = aeq_bs tm1 tm2
>   let runBench (Bench n f x) = bench n $ Criterion.Main.nf f x
>   correctness 
>   defaultMain [
>      bgroup "conv" $ map runBench convs
>    , bgroup "nf"   $ map runBench nfs
>    , bgroup "aeq"  $ map runBench aeqs
>    ]
>
> 


The $\lambda$-expression in {\tt timing.lam} computes
``{\tt factorial 6 == sum [1..37] + 17`factorial 6 == sum [1..37] + 17}'', but using Church numerals.

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
