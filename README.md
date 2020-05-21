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

- DeBruijnC [DB_C]

  (This version doesn't really count because there is no definition 
  of substitution. But it is the fastest!)
  DeBruijn indices without substitutions. Adds a "closure" form to the
  language and uses an environment during normalization.

# Added by SCW

- DeBruijnPar [DB_P]

  Parallel substitution version (with reified substs). Based on
  https://github.com/sweirich/challenge/blob/master/debruijn/debruijn1.md

- DeBruijnParB [DB_B]

  Above, but caches a substitution in terms.
  Uses general purpose library in [Subst](Subst.hs)
  Optimized version described here
  https://github.com/sweirich/challenge/tree/master/debruijn

- DeBruijnScoped [DB_S]

  Above, but uses a GADT to enforce that the syntax is well-scoped.

- BoundDB 

  Uses Kmett's [bound](https://hackage.haskell.org/package/bound) library
  (Note: maybe there is a faster way to convert from named to bound representation.)

- Unbound

  Uses the [unbound](https://hackage.haskell.org/package/unbound) library


## Running the microbenchmark

     make timing
	 
## Latest results	 

Ranked by user time

	DB_C    0m0.003s  (doesn't implement substitution)
	DB_B    0m0.010s
	Bound   0m0.025s
	HOAS    0m0.029s
	DB_P    0m0.852s
	Simple  0m2.316s
	DB      0m3.354s
	Unbound 0m8.932s  (ouch!)
	Unique  0m9.905s

MacBook Pro, 13-inch, Early 2015, 16 GB, Under macOS Catalina 10.15.4

	 time ./LC Simple < timing.lam
	 \x44.\x43.x43

	 real	0m2.664s
	 user	0m2.316s
	 sys	0m0.025s
	 time ./LC Unique < timing.lam
	 \x13663534.\x13663535.x13663535

	 real	0m9.119s
	 user	0m9.017s
	 sys	0m0.062s
	 time ./LC HOAS < timing.lam
	 \x0.\x1.x1

	 real	0m0.046s
	 user	0m0.029s
	 sys	0m0.008s
	 time ./LC DB < timing.lam
	 \x0.\x1.x1

	 real	0m3.698s
	 user	0m3.354s
	 sys	0m0.312s
	 time ./LC DB_C < timing.lam
	 \x0.\x1.x1

	 real	0m0.021s
	 user	0m0.003s
	 sys	0m0.005s
	 time ./LC DB_P < timing.lam
	 \x0.\x1.x1

	 real	0m0.870s
	 user	0m0.852s
	 sys	0m0.011s
	 time ./LC DB_B < timing.lam
	 \x0.\x1.x1

	 real	0m0.019s
	 user	0m0.010s
	 sys	0m0.004s
	 time ./LC Bound < timing.lam
	 \x0.\x1.x1

	 real	0m0.041s
	 user	0m0.025s
	 sys	0m0.007s
	 time ./LC Unbound < timing.lam
	 \x0.\x1.x1

	 real	0m9.964s
	 user	0m8.932s
	 sys	0m0.991s

