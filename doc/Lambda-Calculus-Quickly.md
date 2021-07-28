How to Implement the Lambda Calculus. Quickly
=============================================

Since 1965, the lambda-calculus has been a foundation for our understanding of programming languages [1].  I'm going to assume that you have a basic understanding of what the lambda calculus is, and concepts such as bound & free variables, alpha-equivalence and capture-avoiding substitution.

Syntax
------
    
      a ::= x        variables 
        | \x. a      lambda abstraction
        | a b        application

In a programming langauage, we might implement this using an algebraic datatype of some form, given a type for variable names (i.e. `x`) and for specifying the scope of a bound variable (i.e. `Bind`).

        data Term = 
           | Var Name
           | Lam (Bind Name Term)    -- Bind
           | App Term Term 

Key operations
--------------

* alpha-equivality   

        a ==_\alpha b

    Determine whether two terms are equal, up to the renaming of bound variables. This is a function that returns a boolean value calculated by comparing the terms:

        aeq :: Term -> Term -> Bool

+ capture-avoiding substitution
    
        a { b / x }
    
    Replace all occurrences of free variable x in term a by term b. Make sure that the 
    free variables of b are not "captured" by the bound variables of a. 
    This is also a total function.

        subst :: Var -> Term -> Term -> Term 
        subst x b a = ...

Implementation?
---------------

* How do we represent this language and implement these operations in your favorite programming language? i.e. in Haskell?

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

    We're working in Haskell, so we cannot be too greedy. But we can expect our implementation to apply optimizations (such as cutting off substitution when it is not needed), to maintain sharing (as much as possible), and to avoid quadratic complexity.

Why is this difficult?
----------------------

* Bugs can be subtle and difficult to detect. 

* Because every implementation is for a slightly different language, there is no standard unit test suite. Furthermore, setting up a unit test suite is tedious, because it requires defining many lambda-terms as input + outputs.

* It is not known whether property-based testing is effective for this problem. Can general properties about freevars, boundvars, aeq and subst find bugs in these operations (without comparison to a model implementation)? That would be fun to find out.

* Benchmarking is difficult. These substitutions are general, yet existing implmentations are diverse in their application. So there isn't a representative set of thems.

References
-----------
[1]: Landin, Peter J. Correspondence between ALGOL 60 and Church's Lambda-notation: part I     
https://dl.acm.org/doi/10.1145/363744.363749