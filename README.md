# Lambda-Calculus cooked **n**-ways

This repository is a simple demonstration of various ways to implement
variable binding in Haskell.

It "benchmarks" several different representations of variable binding and
substitution in the untyped lambda calculus using a single pathological case:
computing the normal form of `factorial 6 == sum [1..37] + 17` encoded using
Church numerals. (Spoiler alert, these terms are not equal, so the normal form
is the Church encoding of false).

This is derived from Lennart Augustsson's unpublished draft paper
"Lambda-calculus Cooked Four Ways".


## Contents

1. Original four from Lennart Augustsson's paper:

- Simple

  Naive substitution. Renames variables to avoid capture
  
- Unique

  Maintains the invariant that all bound variables are unique
  
- HOAS

  Higher-order abstract synatax (uses Haskell functions for lambda calculus
  functions)

- Debruijn

  DeBruijn indices that shifts during substitution.

2. Contributed by Bertram Felgenhauer 

- DeBruijnC [DB_C]

  (This version doesn't really count because there is no definition 
  of substitution. But it is the fastest!)
  DeBruijn indices without substitutions. Adds a "closure" form to the
  language and uses an environment during normalization.

3. Added by SCW

- DeBruijnParF [DB_F]
  
  Parallel substitution version, representing substitutions as functions. 

- DeBruijnPar [DB_P]

  Parallel substitution version (with reified substs). Based on
  https://github.com/sweirich/challenge/blob/master/debruijn/debruijn1.md

- DeBruijnParB [DB_B]

  Parallel substitution version with reified substs, but caches a substitution in terms.
  Uses general the purpose library in [Subst](Subst.hs)
  Optimized version described here
  https://github.com/sweirich/challenge/tree/master/debruijn

- DeBruijnScoped [DB_S]

  Above, but also uses a GADT to enforce that the syntax is well-scoped.

- BoundDB 

  Uses Kmett's [bound](https://hackage.haskell.org/package/bound) library
  (Note: maybe there is a faster way to convert from named to bound representation?)

- Unbound

  Uses the [unbound](https://hackage.haskell.org/package/unbound) library

- Core

  Uses the FV and Substitution functions ripped out of GHC Core (HEAD 5/28/20)
  Like DB_C, uses a delayed substitution (e.g. environment) during normalization. 
  Does not add any explicit substitutions to the term.
  Uses Data.IntMap instead of lists to keep track of the substitution. 
  

## Running the microbenchmark

     make timing
	 
## Latest results

See [nf_bench.html](nf_bench.html) and See [aeq_bench.html](aeq_bench.html)
or the [raw results](output.txt).

## References


- https://www.schoolofhaskell.com/user/edwardk/bound
- https://gitlab.haskell.org/ghc/ghc
