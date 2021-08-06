Many implementations come with both strict and lazy variations.


# Original four implementations from Lennart Augustsson

- Lennart.Simple

  Most direct and traditional implementation based on variable names.
  Renames bound variables to avoid capture.
  This version fixes a bug from Lennart's original version.

- Lennart.Unique

  Maintains the invariant that all bound variables are unique. Needs to 
  freshens the binders of terms being substituted to maintain this invariant.
  This version is buggy: see Named.Unique instead.
  
- Lennart.HOAS

  Higher-order abstract synatax (uses Haskell functions for lambda calculus
  functions)

- Lennart.Debruijn

  DeBruijn indices that shift during substitution. Only cosmetic differences with DeBruijn.Lennart.

# de Bruijn indices

##  Variants for "Single substitution"

+ TAPL

The algorithm given in Pierce's Types and Programming Languages, translated from OCaml.

+ DeBruijn.Lennart  (see above)

+ DeBruijn.Cornell/DeBruijn.Lift

  Two versions of an implementation found in the Cornell lecture notes:
  https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf 

+ List (deprecated)

## Variants for "Parallel Substitution"

+ DeBruijn.Par.F
  - substitutions are functions 
+ DeBruijn.Par.L
  - substitutions are infinite lists  (deBruijn's version)
+ DeBruijn.Par.P
  - substs are defunctionalized
    Based on https://github.com/sweirich/challenge/blob/canon/debruijn/debruijn1.md
+ DeBruijn.Par.FB
  - functions delayed at binders
+ DeBruijn.Par.B
  - defunctionalized and delayed at binders, optimized composition
  - uses general the purpose library in Support.Par.Subst
  - described here
    https://github.com/sweirich/challenge/tree/canon/debruijn

+ DeBruijn.Par.GB 
  - like B, but in a library and with GHC.Generics
  - uses Support.Par.Subst

## Well-scoped versions

+ DeBruijn.Nested
  - Bird and Patterson
  - Uses nested datatypes to track scoping level 
  - Only their original version though. For generalized binders, see Bound

+ Chlipala
  - From Adam Chlipala's book "Certified Programming with Dependent Types"
  Originally in Gallina/Coq, but translated to Haskell. 
  Uses DataKinds to ensure that the representation is well-scoped.

+ DeBruijn.Bound
  - uses Kmett's [bound](https://hackage.haskell.org/package/bound)library 
  - based on Bird and Patterson's generalized de Bruijn
  - Nested datatypes ensure that terms stay well-scoped.

+ DeBruijn.Par.Scoped
  - Par.B with strong types
  - uses Support.Par.SubstScoped

+ DeBruijn.Kit
  - Allais et al.
  - Based on code distributed with this paper
    https://dl.acm.org/doi/10.1145/3018610.3018613
  - like F, but with strong types and "finally tagless"


# Locally-Nameless implementations (both strict and lazy)

+ UnboundRep

  Uses the [unbound](https://hackage.haskell.org/package/unbound) library
  
+ UnboundGenerics/UGSubstBind

  Uses Stephanie's fork of the [unbound-generics](https://github.com/sweirich/unbound-generics) library (a port of Unbound that uses GHC.Generics). 

+ Ott/Opt/SupportOpt/GenericOpt

  Various versions that start with the output of Ott's locally nameless backend, and then 
  optimize the deBruijn index portion similar to the Par implementations above.

+ ParScoped/ParOpt

  Use parallel substitutions for bound variables. Also well-scoped.

+ TypedOtt

  Version of the Ott version with types to ensure that terms are locally closed.

# Named representations

- Named.Simple

  Like Lennart.Simple

- Named.NominalG 

  Uses [nominal](https://hackage.haskell.org/package/nominal) package & generic programming

- Named.SimpleH

  Optimizes the "simple" approach by caching the substitution and free variable set at binders. 

- Named.SimpleGH
  Uses library + generic programming to make it easy to use SimpleH.

- Named.SimpleM

  Version of SimpleH that uses a freshness monad to generate fresh variables.


# Other

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

- DeBruijn levels

- Locally-named implementation

- Pollack, Sato, and Riciotti. Canonically-named 
https://link.springer.com/article/10.1007/s10817-011-9229-y

- Abel and Kraus.
https://arxiv.org/pdf/1111.0085.pdf

- McBride, co-debruijn
https://arxiv.org/abs/1807.04085

- NLambda-1.1
https://www.mimuw.edu.pl/~szynwelski/nlambda/doc/
Module supports computations over infinite structures using logical formulas and SMT solving.

- Dolan and White, Shifted names
http://tydeworkshop.org/2019-abstracts/paper16.pdf
https://github.com/lpw25/shifted-names/tree/master/src