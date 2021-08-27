How to Implement the Lambda Calculus, Quickly
=============================================

Alpha-equivalence and capture-avoiding substitution are two fundamental operations in the implementation of the lambda calculus. But, what is the best way to implement these operations in Haskell? I wish I knew.

In this talk, which is part tutorial and part work-in-progress, I'll present what I have learned from gathering many, many implemenations of these operations into the same repository and comparing their execution using a small benchmark suite. 

One observation to make is that that most of these implementations of capture-avoiding substitution require multiple traversals of the AST, which can lead to significant slowdown on larger examples. However, by reifying, delaying, and fusing these traversals, we can dramatically improve performance. Not only that, but I will also show how this optimization can be invisibly incorporated into binding libraries that automatically provide capture-avoiding substitution "for free".

Link to benchmark repository: https://github.com/sweirich/lambda-n-ways

Bio: Stephanie Weirich is a professor of Computer Science at the University of Pennsylvania and has been in love with Haskell and its type system for over twenty years.  