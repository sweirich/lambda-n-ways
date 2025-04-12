# Lambda-Calculus cooked **n**-ways

This repository is focussed on capture-avoiding substitution and alpha-equivalence for the untyped lambda calculus.  It contains benchmarks and implementations of many different implementation strategies and existing libraries for binding support. 

History: The repo was inspired by and initially derived from Lennart Augustsson's unpublished draft paper "Lambda-calculus Cooked Four Ways" and was originally forked from https://github.com/steshaw/lennart-lambda. 

For an overview of the *n*-implementations available here, see [here](doc/Implementations.md).

For a general overview of the project see the slides: [ifl-2021.pptx](doc/ifl-2021.pptx). The plan for this 
talk is also available:
    - [Part 1](doc/Part1.md)
    - [Part 2](doc/Part2.md)
    - [Part 3](doc/Part3.md)
    - [Part 4](doc/Part4.md)
    - [Part 5](doc/Part5.md)

## Compiling the library

This library can be compiled using the stack tool.

The command:

    stack build

will compile the library and produce the executable that can be used for benchmarking.

## Selecting the implementations to run

The source module [Suite](lib/Suite.hs) imports all of the implementations and creates the test/benchmark suite. Modify the variable `impls` in this file to include or exclude various implementations from testing and benchmarking. 

## Running the test suite 

The correctness of the implementations is ensured through quickcheck and unit testing. The module [Main](test/Main.hs) in the `test/` subdirectory defines these tests. To run them:

    stack test

The directory `lams/` contains files of non-normalized lambda-calculus terms that can be used for testing and for benchmarking. In each case, if the file is `test.lam` then a matching file `test.nf.lam` contains the normalized version of the term.

Unit tests based on normalization:
- a single large term (lennart.lam).
- random terms with a small number of substitutions during normalization (onesubst, twosubst...)
- random terms with a large number of substitutions during normalization (random15, random20)
- specially constructed terms (capture10, constructed20) 
- terms that reveal a bug in some implementation (tX, tests, regression)

QuickChecks:
- conversion from/to named representation is identity on lambda terms
- freshened version of random lambda term is alpha-equivalent to original
- normalization on randomly-generated lambda term matches a reference version

## Running the benchmark suite

Overally, the harness is extremely fiddly and requires editing [Main](bench/Main.hs), [Suite](lib/Suite.hs), and the [Makefile](Makefile) to control what implementations are benchmarked with what terms. 

The entry point to the benchmark suite is defined by several targets in the [Makefile](Makefile). Each target produces criterion output in the `results/XXX/YYY` directory, where `XXX` is the name of the machine used to run the benchmark and `YYY` is the value of `impls` in [Suite](lib/Suite.hs). 

    make timing  
       -- alpha equivalence, conversion to/from named rep

    make normalize
       -- normalize large term
       -- normalize groups of 100 randomly generated lambda-terms

    
The benchmarks can also output to individual csv files (one per implementation) using the target. Note that the list in `impls` (in [Suite](lib/Suite.hs)) must be a superset of `$(RESULTS)` for this to work. However, you probably want to comment out the benchmarks in [Main](bench/Main.hs) that you are not running to speed up the harness.

    make csv  

# Benchmark suite

The benchmark suite is defined in the module [Main](bench/Main.hs) in the `bench/` subdirectory. It defines several benchmark groups. 

1. `rand`: Normalization of random lambda terms: 

The 100 randomly-generated terms stored in the file [random15.lam](lams/random15.lam).  

2. `conv`: Conversion to representation: [conv_bench.html](results/conv_bench.html). How long
   does it take to convert a parsed named representation to the internal
   representation of the implementation? alpha-converts the pathological term.
   
3. `nf`:  Normalization of an extremely large lambda term:
  [nf_bench.html](results/nf_bench.html). See below.

```
   bind depth: 25
   depth:      53
   num substs: 119697
```

4. `aeq`: Alpha-equivalence of an extremely large lambda term:
   [aeq_bench.html](results/aeq_bench.html)
   
5. `con`: Normalization for 20 constructed lambda terms
See [file](lams/constructed20.lam).
Each term does a single substitution for an incrementally deeper free variable. This benchmark can be used to estimate the time complexity of the implementation in terms of the binding depth.

6. `capt`: Normalization for 10 capturing lambda terms
See [file](lams/capture10.lam). This file substitutes, at increasing depth, a lambda term with a free variable that could be captured.

### Normalization of a large lambda term

The benchmark is full normalization of the lambda-calculus
term: `factorial 6 == sum [1..37] + 17` represented with a Scott-encoding of
the datatypes. See [lennart.lam](lams/lennart.lam) for the definition of this term.

This "benchmarks" several different representations of variable binding and
substitution in the untyped lambda calculus using a single pathological case:
computing the normal form of `factorial 6 == sum [1..37] + 17`. (Spoiler
alert, these terms are not equal, so the normal form is the encoding of
false).

By full normalization, we mean computing the following partial function that 
repeatedly performs beta-reduction on the leftmost redex.

      nf x         = x
      nf (\x.e)    = \x. nf e
      nf (e1 e2)   = nf ({e2/x}e1')         when whnf e1 = \x.e1'
                    (nf (whnf e1)) (nf e2)       otherwise

      whnf x       = x
      whnf (\x.e)  = \x.e
      whnf (e1 e2) = whnf ({e2/x} e1') when whnf e1 = \x.e1'
                    (whnf e1) e2            otherwise

Note: the goal of this operation is to benchmark the *substitution* function,
written above as {e2/x}e1.  As a result, even though some lambda calculus
implementations may support more efficient ways of computing the normal form
of a term (i.e. by normalizing e2 at most once) we are not interested in
that. Instead, we want the computation to be as close to the 
implementation above as possible.

Because this function is partial (not all lambda-calculus terms have normal
forms), for testing, each implementation also should support a "fueled"
version of the `nf` and `whnf` functions (called `nfi` and `whnfi`,
respectively). However, benchmarking uses the unfueled version.

# Evaluation with booleans

Optionally, *some* implementations have been extended with two additional 
constructs: boolean constants and an if expression. This addition of an 
observable base type allow the benchmarking with evaluation instead of 
normalization. The lambda calculus terms in the `lambs` subdirectory include 
boolean constants, with `eval` marking their final answer.

# Anatomy of an implementation:

Every implementation in this suite matches the following interface:

    data LambdaImpl = forall a.
         NFData a =>
         LambdaImpl
         { impl_name :: String,               -- module name
           impl_fromLC :: LC IdInt -> a,
           impl_toLC :: a -> LC IdInt,
           impl_nf :: a -> a,
           impl_nfi :: Int -> a -> Maybe a,
           impl_aeq :: a -> a -> Bool,
           impl_eval :: a -> a  (optional)
         }

Given some type for the implementation `a`, we need to be able to convert 
to and from that type to a "fully named" representation of lambda-terms. 
(Where the names are just represented by integers).

    data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)

Furthermore, we need to be able to normalize it, using the algorithm specified 
above, and limited by some amount of fuel (for testing). We also need a definition 
of alpha-equivalence.

