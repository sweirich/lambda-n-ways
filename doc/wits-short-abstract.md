Benchmarks binding 
------------------

Implementations of type systems, logics and programming languages must often
answer the question of how to represent and work with binding structures in
terms. While there may not be a one-size-fits-all solution, I would like to
understand the trade-offs that various approaches to binding make in terms of
execution speed and simplicity of implementation.  To that end, I have been
constructing a benchmark platform using the Haskell programming language and
have been gathering multiple implementations of binding for [comparison and
experimentation](https://github.com/sweirich/lambda-n-ways).

I plan to use this repository as a focus for a discussion about the following
questions related to aggregating and comparing implementations of binding.

* What should a benchmark suite contain? Should the focus be on substitution,
  normalization, alpha-equivalence, or other operations? So far, I've focused
  my efforts on capture-avoiding substitution, but what other operations are
  important?

* What optimizations can we evaluate? Delaying fusing and discarding trivial
  substitutions seems to be effective, are there other ways to optimize these
  operations?

* What about library support? What is the cost of providing a simple interface
  to these operations? 

* What is used in practice?
