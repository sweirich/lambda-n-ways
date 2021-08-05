How to Implement the Lambda Calculus, Quickly
=============================================

Since 1965, the lambda-calculus has been a foundation for our understanding of programming languages [1].  I'm going to assume that you have a basic understanding of what the lambda calculus is, and concepts such as bound & free variables, alpha-equivalence and capture-avoiding substitution. On paper, we might write the lambda calculus using the following BNF, and then say things like "the variable x is bound in the scope of a" or "we identify terms up to alpha-equivalence and adopt the Barandregt Bound Variable convention".
    
      a ::= x        variables 
        | \x. a      lambda abstraction
        | a b        application

However, when programming we must be more explicit. We might implement this using an algebraic datatype of some form, given a type for variable names (i.e. `Var`) and for specifying the scope of a bound variable (i.e. `Bind`).

        data Exp = 
           | Var Var           -- occurrence of a variable
           | Lam (Bind Exp)    -- create a binder for the variable
           | App Exp Exp 

The lambda calculus itself comes with two key operations on expressions. The first, *alpha-equivalence* is a function that determines whether two terms are equal, up to the renaming of bound variables. On paper, we might write this function as 

        a ==_alpha b

For example, we have that 

        \x.x ==_alpha \y.y

evaluates to true. Analogously, in our implementation, we need a function that determines the alpha-equivalence of expressions above. 

        aeq :: Exp -> Exp -> Bool

We also need substitution function that replaces all occurrences of free variable `x` in term `a` by term `b`, written,
    
        a { b / x }
    
that is careful to avoid variable capture. For example, 

        (\y.x) { y / x }

should evaluate to 

        (\w.y)

where the bound variable has been renamed so it doesn't interfere with the free variable 'y'. Because we assume that there are a finite number of free variables, and an infinite number of variables total, we can always find new variable names that won't capture. Therefore we can define a total function:

        subst :: Var -> Exp -> Exp -> Exp 
        subst x b a = ...

Implementation?
---------------

This is all very abstract, but how should fill in the details? Unfortunately, we have a wealth of answers, even sticking with first-order representations.

- Names: simple renaming, BVC 
- Names: nominal
- de Bruijn indices
- de Bruijn levels
- co-de Bruijn representation
- HOAS
- Weak HOAS / PHOAS
- Locally Nameless
- Locally Named
- Canonically Named

These implementations differ in
- Representation of syntax, esp. variables and binders
- Implementation of alpha-equivalence, capture-avoiding substitution functions
- What you need to do to implement other operations

* What should we think about when selecting an implementation?

* Of course, if we only had to implement these operations for this language, we'd be done already. However, we want a general notion of translating the ideas of variable occurrences and binding to arbitrary languages, and implementing these operations in that context.

* Let's call that a *binding implementation*.

What do we want from a binding implementation?
---------------------------------------

* Quick development, with confidence

    These operations are *standard* and, in many cases, *datatype-generic*. An ideal world provides us with libraries where we can declarative specify the information needed to generate the algorithm for our data type definition. 

* An interface that helps us use these operations safely

    Depending on what we choose for our implementation, `aeq` or `subst` may or may not have the types given above. Furthermore, there may be some invariants that must be maintained about our code, when we call these operations...

* Fast-ish execution

    We're working in Haskell, so we cannot be too greedy. But we would like an implementation to apply optimizations (such as cutting off substitution when it is not needed), to maintain sharing (as much as possible), and to avoid quadratic complexity.

Why is this difficult?
----------------------

* Bugs can be subtle and difficult to detect. 

* Because every implementation is for a slightly different language, there is no standard unit test suite. Furthermore, setting up a unit test suite is tedious, because it requires defining many lambda-terms as input + outputs.

* It is not known whether property-based testing is effective for this problem. Can general properties about freevars, boundvars, aeq and subst find bugs in these operations (without comparison to a model implementation)? That would be fun to find out.

* Benchmarking is difficult. These substitutions are general, yet existing implmentations are diverse in their application. So there isn't a representative set of thems.

Contributions
--------------

1. A library of various implmentations and variations of the untyped lambda calculus. In this project, we limit ourselves to *pure* implementations, i.e. those that can instantiate the general skeleton above. This means that some approaches are off-limits; we cannot, say, represent variables by pointers to their binding locations, relying on the properties of heap layout to ensure that the barandregt variable convention is maintained. Working in Haskell, we cannot even observe the sharing in our data structures, so we'll have to think about that externally (and carefully).

The advantage of this constraint is that it keeps us closer to implementations that we can implement and verify in a proof assistant like Agda or Coq. Because Haskell allows nontermination, we can't be sure that a Haskell definition can be ported over to Coq/Agda directly (and the termination arguments for substitution are often subtle!). However, nontermination is the only effect that we have to worry about so perhaps this work can lead to faster implementations within proof assistants.

Pure implemnations also have other benefits when it comes to programming, especially when thinking about invariants that must be maintained when using these data structures.

2. A test suite that verifies the correctness of these implementations.

This repository is public and others are encouraged to add to it. However, there are many incorrect implementations floating around, so we need to make sure that we only compare correct ones. Yet, asking everyone to produce a proof of correctness seems too much. 

3. A benchmark suite to compare the running time. 

Inspired by Lennart Augustson's "Lambda Calculus Cooked Four Ways" [4], this project contains a benchmarking suite that is based on full normalization. Normalization for lambda-calculus terms involves many repeated calls to substitution, so we can time calls to this function on various lambda terms to compare implementations. 

Note, we are not trying to implement reduction quickly: just substitution. If we want to speed up reduction itself, we wouldn't use substitution at all, we'd switch to a virtual machine. Similarly, our reduction function doesn't reduce terms using the fewest number of substituions, it is possible to do much better using alternative reduction algorithms. (See "optimal reduction"). That is not what we are on about.




References
-----------
[1]: Landin, Peter J. Correspondence between ALGOL 60 and Church's Lambda-notation: part I     
https://dl.acm.org/doi/10.1145/363744.363749
[2]: de Bruijn. 
[3]: Barendregt, Henk. The Lambda Calculus, Its Syntax and Semantics. North Holland, 1984.
[4]: Augustsson, Lennart. Lambda Calculus Cooked Four Ways. Draft paper and implementation, available from https://github.com/steshaw/lennart-lambda/