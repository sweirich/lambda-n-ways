Optimization
------------

In all three of these examples, we can see that we have to do multiple traversals of the term, to freshen variables, to shift indices, or to open and close binders. 

We can keep the same interface but dramatically improve the performance by generalizing these traversals to n-ary forms, reifying them as a data structure, and then caching them at binders so that they can be dynamically fused.  

* [Named.SimpleH](lib/Named/SimpleH.hs)

   For named representation, this means defining a multi-substitution operation, representing substitutions using a finite map from identifiers to expressions.

        type Sub a = IdMap a 

        subst :: Sub Exp -> Exp -> Exp

   Store a set of free variables at every binder.

        data Bind a = Bind
        { 
          bind_fvs :: !VarSet,     -- cached set of free variables in the body
          bind_var :: !IdInt,
          bind_body :: !a
        }

  When we substitute through a binder, we do two things:
    + trim the substitution so that its domain only includes to the free variables of the term
    + compose it with any necessary renamings to avoid variable capture


* [DeBruijn.Par.B](lib/DeBruijnPar/B.hs)

We can also delay bound variable substitution. This is even easier because we can draw on the theory of 
explicit substitutions.
 
        subst :: Sub Exp -> Exp -> Exp   -- substitute for *all* indices in the expression.

        data Sub a
        = Inc !Int                -- shift
        | Cons a !(Sub a)         -- add a new binding
        | !(Sub a) :<> !(Sub a)   -- compose two substitutions
        deriving (Show)

        data Bind a = Bind !(Sub a) !a    -- cached substitution

        subst s2 (Bind s1 e) = Bind (s1 `comp` lift s2) e -- compose substitutions at binders

The key idea that makes this work is that we can optimize when we compose.

        comp :: Sub Exp -> Sub Exp -> Sub Exp
        comp (Inc k1) (Inc k2) = Inc (k1 + k2)
        comp (Inc 0) s = s
        comp (Inc n) (Cons _t s)
        | n > 0 = comp (Inc (n - 1)) s
        comp s (Inc 0) = s
        comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
        comp (Cons t s1) s2 = Cons (subst s2 t) (comp s1 s2)
        comp s1 s2 = s1 :<> s2

* [LocallyNameless.Opt](lib/LocallyNameless/SupportInstOpt.hs)

Finally, this idea also works for locally nameless implementation. 

[TODO: explain...]

[Next page](Part4.md)