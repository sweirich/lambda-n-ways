Overview of DeBruijn index based implementations.

* Variants for "Single substitution"

+ Lennart
+ Lift
+ Cornell 
+ List 

* Variants for "Parallel Substitution"

Many of these variants can be seen as an adaptation of lambda-sigma
"Explicit Substitutions"
https://www.hpl.hp.com/techreports/Compaq-DEC/SRC-RR-54.pdf

+ DeBruijn.Par.F
  - substitutions are functions
+ DeBruijn.Par.L
  - substitutions are infinite lists 
+ DeBruijn.Par.P
  - substs are defunctionalized
+ DeBruijn.Par.FB
  - functions delayed at binders
+ DeBruijn.Par.B
  - defunctionalized and delayed at binders

* Well-scoped versions

+ DeBruijn.Nested
  - Bird and Patterson
  - Uses nested datatypes to track scoping level 
+ Chlipala
  - From CPDT, translated from Gallina
+ DeBruijn.Bound
  - uses Kmett's library 
+ DeBruijn.Par.Scoped
  - Par.B with strong types.
+ DeBruijn.Kit
  - Allais et al.
  - like F, but with strong types and "finally tagless"