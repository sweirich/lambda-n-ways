This is a fork of Lennart Augustsson's lambda-calculus cooked four ways. 

It "benchmarks" several different representations of variable binding and
substitution using a single pathological case: computing the normal form of
`factorial 6 == sum [1..37] + 17` encoded using Church numerals.

## Contents

# Original four:

- Simple
  Naive substitution. Renames variables to avoid capture
  
- Unique
  Maintains the invariant that all bound variables are unique
  
- HOAS
  Higher-order abstract synatax (uses Haskell functions for lambda calculus
  functions)

- Debruijn
  DeBruijn indices that shifts during substitution.

# Contributed by Bertram Felgenhauer 

- DeBruijnC
  (This version doesn't really count because there is no definition 
  of substitution. But it is the fastest!)
  DeBruijn indices without substitutions. Adds a "closure" form to the
  language and uses an environment during normalization.

# Added by SCW

- DeBruijnPar
  Parallel substitution version (uwith reified substs). Similar to 
  https://github.com/sweirich/challenge/blob/master/debruijn/debruijn1.md

- DeBruijnParB
  Above, but caches a substitution in terms.
  Optimized version described here
  https://github.com/sweirich/challenge/tree/master/debruijn

- BoundDB
  Uses Kmett's [bound](https://hackage.haskell.org/package/bound) library

- Unbound
  Uses the [unbound](https://hackage.haskell.org/package/unbound) library
  (Currently WIP)

## Running the microbenchmark

     make timing
	 
## Latest results	 

MacBook Pro, 13-inch, Early 2015, 16 GB, Under macOS Catalina 10.15.4

	time ./LC Simple < timing.lam
	\x44.\x43.x43

	real	0m2.701s
	user	0m2.383s
	sys	0m0.070s
	time ./LC Unique < timing.lam
	\x13663534.\x13663535.x13663535

	real	0m10.375s
	user	0m9.905s
	sys	0m0.225s
	time ./LC HOAS < timing.lam
	\x0.\x1.x1

	real	0m0.050s
	user	0m0.033s
	sys	0m0.007s
	time ./LC DB < timing.lam
	\x0.\x1.x1

	real	0m4.026s
	user	0m3.585s
	sys	0m0.367s
	time ./LC DB_C < timing.lam
	\x0.\x1.x1

	real	0m0.021s
	user	0m0.003s
	sys	0m0.004s
	time ./LC DB_P < timing.lam
	\x0.\x1.x1

	real	0m0.896s
	user	0m0.856s
	sys	0m0.023s
	time ./LC DB_B < timing.lam
	\x0.\x1.x1

	real	0m0.018s
	user	0m0.010s
	sys	0m0.005s
	time ./LC Bound < timing.lam
	\x0.\x1.x1

	real	0m0.041s
	user	0m0.028s
	sys	0m0.008s
