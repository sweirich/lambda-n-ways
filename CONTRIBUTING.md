Pull requests with enhanced documentation, new implementations and new lambda terms to normalize for testing/benchmarking are welcome!

How to add a new lambda calculus implementation to this benchmark suite
---------------

1. Create a new module under `lib/XXX/` where `XXX` is a high-level approach. Currently we have `DeBruijn`, `LocallyNameless` or `Named`. If your version is a variant of one of these, add your module there. If it is a new approach, make a new directory for it.

2. If you want to split your implementation into binding library/client put the library in `lib/Support/`.

3. Your module must import a value `impl` of type `LambdaImpl`, defined in the module `Util.Impl`. 

        data LambdaImpl = forall a.
          NFData a =>
          LambdaImpl
          { impl_name :: String,
              -- ^ the name of the module
            impl_fromLC :: LC IdInt -> a,
            impl_toLC :: a -> LC IdInt,
              -- ^ conversion to/from a named representation
            impl_nf :: a -> a,
              -- ^ normalization function
            impl_nfi :: Int -> a -> Stats.M a,
              -- ^ bounded version of normalization function, for testing
              -- optional
            impl_aeq :: a -> a -> Bool
              -- ^ alpha-equivalence function
        }

4. You can define your own data type to represent lambda calculus terms or use the one (`LC`) provided in `Util.Syntax.Lambda`. Other modules in `lib/Util` and `lib/Support` may be useful for you. 

5. Don't forget to add your new module(s) to the `lambda-n-ways.cabal` file!

6. Import your new module in `lib/Suite.hs` and add it to some list of implementations. Update the variable `all_impls` to refer to the suite that includes yours.

7. Test using `stack test lambda-n-ways`. The tests that are run are listed in `tests/Main.hs` 
       
8. Benchmark using the Makefile. `make normalize` will run the normalization benchmark and produce html output.

How to add new lambda terms for the normalization benchmarks
-----------

1. The `lams` subdirectory contains suites of lambda terms used for benchmarking and testing. Each file contains one or more lambda-calculus expressions and should be accompanyied by a `.nf` version containing their normal forms.

2. You can automatically generate the .nf version (and the stats) using the functions in `lib/QuickBench` module.

3. Edit tests/Main.hs and bench/Main.lhs to load your new lambda terms.

