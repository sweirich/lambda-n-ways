# Implementing the lambda calculus

The lambda calculus is easy to define, but only because we already know it works. If we have to teach it to someone who doesn't understand (like our compiler) then we suddenly realize just how subtle the definitions are. And how many ways the lambda calculus can be implemented. 

This paper takes as a starting point Lennart Augusston's "Lambda calculus cooked four ways", which demonstrates how to implement the lambda calculus using
* (HOAS) Higher-order abstract syntax
* (DeBruijn) Debruijn indices
* (Simple) A named representation, where bound variables are renamed if they would ever capture. 
* (Unique) A named representation, where all bound variables must be globally unique

When benchmarking lambda calculus implementations, sometimes things get caught up in optimal beta-reduction. We don't want to go there. So in this setting we will be absolutely rigid about our benchmarking routine: we are going to do normal order reductions of the lambda calculus. We're benchmarking substitution after all and beta-reduction incurs a *lot* of substitutions. There are many ways to cut down the number of substitutions that you need, but that would undercut our purpose: we want to isolate substitution so that we can measure it directly.



------------------------