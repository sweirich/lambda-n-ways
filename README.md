# Lambda-Calculus cooked **n**-ways

This repository is an experiment in implementing capture-avoiding substitution and alpha-equivalence for the untyped lambda calculus.  It contains benchmarks and implementations of many different implementation strategies and existing libraries for binding support. 

History: This repo is derived from Lennart Augustsson's unpublished draft paper
"Lambda-calculus Cooked Four Ways" and was originally forked from https://github.com/steshaw/lennart-lambda. 

## Compiling the library

This library can be compiled using the stack tool, using resolver: https://www.stackage.org/lts-15.14
This pins the implementation to GHC version 8.8.3, which is the most recent implementation of GHC supported by the RepLib and Unbound libraries. More recent versions of GHC can be used for benchmarking if Unbound is removed from the test suite. 

The command:

    stack build

will compile the library and produce the `LC` executable that can be used for benchmarking.

## Selecting the implementations 

The source module [Suite](lib/Suite.hs) imports all of the various implementations and creates the test suite. Modify this file to include or exclude various implementations from testing and benchmarking. 

## Running the test suite 

The correctness of the various implementation is ensured through quickcheck and unit testing. The module [Main](test/Main.hs) in the `test/` subdirectory defines these tests.

    stack test

The directory `lams/` contains files of non-normalized lambda-calculus terms. In each case, if the file is `test.lam` then a matching file 
`test.nf.lam` contains the normalized version of the term.

Unit tests:
- pathological term (lennart.lam).
- random terms with a small number of substitutions during normalization (onesubst, twosubst...)
- random terms with a large number of substitutions during normalization (random25, random35,lams100)
- constructed terms (capture10, constructed20) 
- terms that reveal a bug in some implementation (tX, tests, regression)

QuickChecks
- conversion from/to named representation is identity on lambda terms
- freshened version of random lambda term is alpha-equivalent to original
- nf on random lambda term matches a reference version (DeBruijn.Lennart)
   (This test uses a "fueled version" of normalization)

## Running the benchmark suite

    make timing

# Benchmark suite

The benchmark suite is defined in the module [Main](bench/Main.hs) in the `bench/` subdirectory. It defines several benchmark groups. 

1. `rand`: Normalization of random lambda terms: 
[rand_bench.html](results/rand_bench.html).

The 25 randomly-generated terms stored in the file [random.lam](lams/random.lam).  They are
generated via `genScopedLam` in [Lambda.lhs](lib/Lambda.lhs) with size
parameter `100000`, and so are closed and contain lots of
lambdas. Normalizing these terms requires between 26-177 calls to `subst`. The
terms themselves have total depth from 36-73 and binding depth from 23-57.

2. `conv`: Conversion to representation: [conv_bench.html](results/conv_bench.html). How long
   does it take to convert a parsed named representation to the internal
   representation of the implementation? alpha-converts the pathological term.
   
3. `nf`:  Normalization of a pathological lambda term:
  [nf_bench.html](results/nf_bench.html). See below.

```
   bind depth: 25
   depth:      53
   num substs: 119697
```

4. `aeq`: Alpha-equivalence of a pathological lambda term:
   [aeq_bench.html](results/aeq_bench.html)
   
5. `con`: Normalization for 20 constructed lambda terms
See [file](lams/constructed20.lam).
Each term does a single substitution for an incrementally deeper free variable. This benchmark can be used to estimate the time complexity of the implementation in terms of the binding depth.

6. `capt`: Normalization for 10 capturing lambda terms
See [file](lams/capture10.lam). This file substitutes, at increasing depth, a lambda term with a free variable that could be captured.

### Normalization microbenchmark

The microbenchmark is full normalization of the lambda-calculus
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
enabling that computation. Instead, we want the computation to be as close to the 
implementation above as possible.

Because this function is partial (not all lambda-calculus terms have normal
forms), for testing, each implementation also should support a "fueled"
version of the `nf` and `whnf` functions (called `nfi` and `whnfi`,
respectively). However, benchmarking uses the unfueled version.

# Anatomy of an implementation:

Every implementation in this suite matches the following interface:

    data LambdaImpl = forall a.
         NFData a =>
         LambdaImpl
         { impl_name :: String,
           impl_fromLC :: LC IdInt -> a,
           impl_toLC :: a -> LC IdInt,
           impl_nf :: a -> a,
           impl_nfi :: Int -> a -> Maybe a,
           impl_aeq :: a -> a -> Bool
         }

Given some type for the implementation 'a', we need to be able to convert 
to and from that type to a "fully named" representation of lambda-terms. 
(Where the names are just represented by integers).

    data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)

Furthermore, we need to be able to normalize it, using the algorithm specified 
above, and limited by some amount of fuel (for testing). We also need a definition 
of alpha-equivalence for this representation.

# The n implementations

Original four implementations from Lennart Augustsson's paper:

- Simple

  Most direct and traditional implementation based on variable names.
  Renames bound variables to avoid capture.
  
- Unique

  Maintains the invariant that all bound variables are unique. Needs to 
  freshens the binders of terms being substituted to maintain this invariant.
  
- HOAS

  Higher-order abstract synatax (uses Haskell functions for lambda calculus
  functions)

- Debruijn

  DeBruijn indices that shift during substitution.

## DeBrujn-index based implementations

- Bound

  Uses Kmett's [bound](https://hackage.haskell.org/package/bound) library.
  Nested datatypes ensure that terms stay well-scoped.

- Kit

  Based on code distributed with this paper
  https://dl.acm.org/doi/10.1145/3018610.3018613

- TAPL

  The algorithm given in Pierce's Types and Programming Languages.

- Chlipala

  From Adam Chlipala's book "Certified Programming with Dependent Types"
  Originally in Coq, but translated to Haskell. Uses DataKinds to ensure that 
  the representation is well-scoped.

- Lift/Cornell

Two versions of an implementation found in the Cornell lecture notes:
https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf

- Nested 

Extracted from "de Bruijn notation as a nested datatype",
by Richard S. Bird and Ross Paterson
(renamed and adapted to this benchmark framework).

- DeBruijn.Par.F 
  
  Parallel substitution version, representing substitutions as functions. 

- DeBruijn.Par.L

  Represents substitutions as infinite lists

- DeBruijn.Par.FB 
  
  Parallel substitution version, representing substitutions as functions. 
  Introduces a 'Bind' abstract type to cache substitutions at binders.

- DeBruijn.Par.P 

  Parallel substitution version (with reified substs). Based on
  https://github.com/sweirich/challenge/blob/canon/debruijn/debruijn1.md

- DeBruijn.Par.B 

  Parallel substitution version with reified substs, but caches a substitution in terms.
  Uses general the purpose library in [Subst](Subst.hs)
  Optimized version described here
  https://github.com/sweirich/challenge/tree/canon/debruijn

- DeBruijn.Par.Scoped 

  Above, but also uses a GADT to enforce that the syntax is well-scoped.


## Locally-Nameless implementations

- Unbound

  Uses the [unbound](https://hackage.haskell.org/package/unbound) library
  
- UnboundGenerics

  Uses the [unbound-generics] library (a port of Unbound that uses GHC.Generics)

- Ott/Opt/Par/ParOpt

  Various versions that start with the output of Ott's locally nameless backend, and then 
  optimize the deBruijn index portion similar to the Par implementations above.

- Typed/TypedOpt

  Version of the Ott etc versions with types to ensure that terms are locally closed.

## Named representations

- NominalG 

  Uses [nominal](https://hackage.haskell.org/package/nominal) package & generic programming

- SimpleH

  Optimizes the "simple" approach by caching the substitution and free variable set at binders. 

- SimpleM

  Version of SimpleH that uses a freshness monad to generate fresh variables.


## Other

- Core

  Uses the FV and Substitution functions ripped out of GHC Core (HEAD as of 5/28/20)
  This file uses a delayed substitution (e.g. environment) during normalization. 
  Does not add any explicit substitutions to the term.
  Uses Data.IntMap instead of lists to keep track of the substitution. 
  

# References

- repo this is forked from (and Lennart's draft paper)
- https://www.schoolofhaskell.com/user/edwardk/bound
- https://gitlab.haskell.org/ghc/ghc

## Missing implementations

DeBruijn levels

Locally-named implementation

GHC Core type-level substitution

Canonically-named 
https://link.springer.com/article/10.1007/s10817-011-9229-y

https://arxiv.org/pdf/1111.0085.pdf

https://www.mimuw.edu.pl/~szynwelski/nlambda/doc/
Module supports computations over infinite structures using logical formulas and SMT solving.