> {-# LANGUAGE BangPatterns #-}
> {-# LANGUAGE RecordWildCards #-}
> 
> {- | Entry point for the benchmarking application. 
>      
>  -}
> module Main where
> import qualified Data.List as List
> import Util.Misc ()
> import Util.Syntax.Lambda ( LC(..) )
> import Util.IdInt ( IdInt )
> import Util.Impl ( LambdaImpl(..), toIdInt, getTerm, getTerms, lambdaFalse )
> import Suite ( impls )
> import qualified Named.Simple as Simple
> import qualified Named.Unique as Unique
> import Test.QuickCheck ()
> import System.IO.Unsafe ( unsafePerformIO )

> import Criterion.Main ( defaultMain, bench, bgroup, nf, Benchmark )
> import Control.DeepSeq ( force, NFData(rnf) )

> -- | A benchmark is either a single test, or a named group of tests.
> data Bench =
>   forall a. Bench String (a -> ()) a
>   | BGroup String [Bench]


> -- | Benchmarks for timing conversion *from* named representation to internal representation
> conv_bs :: LC IdInt -> [Bench]
> conv_bs lc = lc `seq` map impl2nf impls where
>   impl2nf :: LambdaImpl -> Bench
>   impl2nf LambdaImpl {..} =
>     Bench impl_name (rnf . impl_fromLC) lc

> assertAll :: [Bool] -> Bool
> assertAll (True : xs) = assertAll xs
> assertAll [] = True
> assertAll (False : xs) = assertAll xs -- error "error: assertAll FAILED!!!!" 

> -- | Benchmarks for timing normal form calculation (multiple terms)
> nf_bss :: [LC IdInt] -> [LC IdInt] -> [Bench]
> nf_bss lcs nflcs = map impl2nf impls where
>   impl2nf LambdaImpl {..} =
>     let !tms = force (map impl_fromLC lcs) in
>     let !nftms = force (map impl_fromLC nflcs) in
>     Bench (impl_name <> "/") (rnf . assertAll . ((map (\(t,r) -> impl_aeq (impl_nf t) r)))) (zip tms nftms)


> -- | Benchmarks for timing evaluation (multiple terms)
> eval_bss :: [LC IdInt] -> [LC IdInt] -> [Bench]
> eval_bss lcs nflcs = map impl2nf impls where
>   impl2nf LambdaImpl {..} =
>     let !tms = force (map impl_fromLC lcs) in
>     let !nftms = force (map impl_fromLC nflcs) in
>     Bench (impl_name <> "/") (rnf . (map (\(t,r) -> impl_aeq (impl_eval t) r))) (zip tms nftms)


> -- | Benchmarks for timing normal form calculation (multiple groups of multiple terms)
> constructed_bss :: String ->[LC IdInt] -> [Bench]
> constructed_bss nm lcs = map impl2nf impls where
>   impl2nf LambdaImpl {..} =
>     let !tms = force (map impl_fromLC lcs) in
>     let benches = map (\(t,i) -> Bench (show (i::Int)) (rnf . impl_nf) t) (zip tms [1..]) in
>     BGroup (impl_name <> "/" <> nm) benches


> -- benchmark for comparing alpha-equivalence
> aeq_bs :: LC IdInt -> LC IdInt -> [Bench]
> aeq_bs lc1 lc2 = map impl2aeq impls where
>   impl2aeq LambdaImpl {..} =
>     let !tm1 = force (impl_fromLC lc1) in
>     let !tm2 = force (impl_fromLC lc2) in
>     Bench impl_name (\(x,y) -> rnf (impl_aeq x y)) (tm1,tm2)


> -- | Freshen Lennart's term and compare for alpha equivalence
> aeq_fresh_bs :: LC IdInt -> [Bench]
> aeq_fresh_bs lennart = do 
>   let tm2 = toIdInt (Unique.fromUnique (Unique.toUnique lennart))
>   aeq_bs lennart tm2


> runBench :: Bench -> Benchmark
> runBench (Bench n f x) = bench n $ Criterion.Main.nf f x
> runBench (BGroup n bs) = bgroup n $ map runBench bs

> main :: IO ()
> main = do
>   lennart <- toIdInt <$> getTerm "lams/lennart.lam"
>   lennartb <- toIdInt <$> getTerm "lambs/lennartb.lam"
>   lennartb5 <- toIdInt <$> getTerm "lambs/lennartb5.lam"
>   lennartb4 <- toIdInt <$> getTerm "lambs/lennartb4.lam"
>   lennartC <- toIdInt <$> getTerm "lambs/lennartchurch.lam"
>   random15_terms <- getTerms "lams/random15.lam"
>   random15_nfterms <- getTerms "lams/random15.nf.lam"
>   random20_terms <- getTerms "lams/random20.lam"
>   random20_nfterms <- getTerms "lams/random20.nf.lam"
>   random25_terms <- getTerms "lams/random25.lam"
>   random25_nfterms <- getTerms "lams/random25.nf.lam"
>   random35_terms <- getTerms "lams/random35.lam"
>   random35_nfterms <- getTerms "lams/random35.nf.lam"
>   onesubst_terms <- getTerms "lams/onesubst.lam"
>   twosubst_terms <- getTerms "lams/twosubst.lam"
>   threesubst_terms <- getTerms "lams/threesubst.lam"
>   foursubst_terms <- getTerms "lams/foursubst.lam"
>   id_terms <- getTerms "lams/id.lam"
>   con_terms <- getTerms "lams/constructed20.lam"
>   capt_terms <- getTerms "lams/capture10.lam"
>   adjust_terms <- getTerms "lams/adjust.lam"
>   adjustb_terms <- getTerms "lams/adjustb.lam"
>   defaultMain [
>      bgroup "random15" $ map runBench (nf_bss random15_terms random15_nfterms)
>    , bgroup "random20" $ map runBench (nf_bss random20_terms random20_nfterms)
>    , bgroup "random25" $ map runBench (nf_bss random25_terms random25_nfterms)
>    , bgroup "random35" $ map runBench (nf_bss random35_terms random35_nfterms)
> {-   , bgroup "onesubst" $ map runBench (nf_bss onesubst_terms)
>    , bgroup "twosubst" $ map runBench (nf_bss twosubst_terms)
>    , bgroup "threesubst" $ map runBench (nf_bss threesubst_terms)
>    , bgroup "foursubst" $ map runBench (nf_bss foursubst_terms) -}
>    --, bgroup "conv" $ map runBench (conv_bs lennart)  
>    , bgroup "nf"   $ map runBench (nf_bss [lennart] [lambdaFalse]) 
>    --, bgroup "aeq"  $ map runBench (aeq_fresh_bs lennart)
>    --, bgroup "aeqs" $ map runBench (aeq_bs lennart lennart) 
>    , bgroup "eval" $ map runBench (eval_bss [lennartb] [Bool False])
>    --, bgroup "eval5" $ map runBench (eval_bss [lennartb5] [Bool False])
>    --, bgroup "eval4" $ map runBench (eval_bss [lennartb4] [Bool False])
>    --, bgroup "evalC" $ map runBench (eval_bss [lennartC] [Bool False])
>    {-  bgroup "ids" $ map runBench (constructed_bss "ids" id_terms)
>    , bgroup "con"  $ map runBench (constructed_bss "con" con_terms)
>    , bgroup "capt" $ map runBench (constructed_bss "capt" capt_terms) 
>    , bgroup "adjust" $ map runBench (constructed_bss "adjust" adjust_terms)
>    , bgroup "adjustb" $ map runBench (constructed_bss "adjustb" adjustb_terms)  -}
>    ] 
>
>
>

The $\lambda$-expression in {\tt lennart.lam} computes
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
