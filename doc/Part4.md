(Generic) Binding libraries
===========================

Each of these three implementations can be given very similar library interfaces, where all of the tricky stuff is hidden from the user. And these interfaces can *also* be automatically instantiated via generic programming. 

In other words, substitution and equality can automatically be generated from the structure of the expression datatype. 

* A binding library for Named representation

Let's take a look to see how this works by looking at the library
[SubstH](../lib/Support/SubstH.hs) that provides support for name-based 
implementations.

The job of the binding library is to provide a declarative approach to variable binding. 

    type Var = V IdInt             -- concrete, we know we are working with names
    type Bind a                    -- abstract
    type Sub a                     -- abstract

We also have constructors and destructors for our abstract types.

    bind :: Var -> a -> Bind a     
    unbind :: Bind a -> (Var, a)

    emptySub :: Sub a
    singleSub :: Var -> a -> Sub a
    

The key part of the library is the declarations of the (overloaded) functions:

    class VarC a where
      var :: Var -> a                -- ASTs that include variables

    class FreeVarsC a where
      freeVars :: a -> VarSet        
  
    class FreeVarsC a => SubstC b a where
      subst :: Sub b -> a -> a

plus instances for the `Var` and `Bind` types defined in the library.

    instance FreeVarsC Var 
    instance FreeVarsC a => FreeVarsC (Bind a)

    substVar :: VarC a => Sub a -> Var -> a 
    instance SubstC a a => SubstC a (Bind a)

These overloaded functions allow the client and library code to communicate. The library needs to automatically rename bound variables when substituting through a binding. To do that, it needs to know how to calculate the free variables of an expression, create a new substitution that renames a variable, and apply that substitution.


* Named library usage 

In the client code, the library functions and instances make the 
definitions straightforward traversals of the expression datatype.


    data Exp
      = Var !Var
      | Lam !(Bind Exp)
      | App !Exp !Exp
      deriving (Eq, Generic)

    instance VarC Exp where
      var = Var

    instance FreeVarsC Exp where
      freeVars (Var v) = freeVars v
      freeVars (Lam b) = freeVars b
      freeVars (App f a) = freeVars f `S.union` freeVars a

    instance SubstC Exp Exp where
      subst s (Var v) = substVar s v
      subst s (Lam b) = Lam (subst s b)
      subst s (App f a) = App (subst s f) (subst s a)

Note: the definition of the Eq instance for Bind substitutes if the variables 
do not match. So, the derived instance (Eq) is alpha-equivalence!

* Named Generic Library

Furthermore, if we extend these definitions with a function that 
determines what part of the expression is a variable, we can also
teach the library to have default definitions for free vars and 
substitution.

    data Exp
      = Var !Var
      | Lam !(Bind Exp)
      | App !Exp !Exp
      deriving (Generic, Eq)

    instance VarC Exp where
      var = Var
      isvar (Var v) = Just v
      isvar _ = Nothing

    instance FreeVarsC Exp where
    instance SubstC Exp Exp where

So, 11 lines of code total, excluding the module imports.

This treatment is not unique to the named representation, we can also define similar libraries for de Bruijn indices and for locally nameless representation.

* Benchmark

But what is the cost of this genericity? Generic programming does have a small effect on runtime, but it is not much compared to the win we gain from using our optimized library. Furthermore, the same library can be used without generic programming by providing the straightforward traversals by hand.

[Next page](Part5.md)