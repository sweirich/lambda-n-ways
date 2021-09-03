Some concrete implementations of capture-avoiding substitution
==============================================================

Normal-order full reduction
---------------------------

Our main benchmark for comparison is based on Normal-order full reduction.

This function beta-reduces a lambda term everywhere, including under binders. In this variant, arguments are substituted into the body of a binder before they are reduced (i.e. the leftmost, outermost reduction happens first)
If an expression has a normal form, then normal order evaluation will always find it.

For example: this term

       (λx. y) ((λx. x x) (λx. x x))

reduces to 

        y

because the infinite loop is discarded before reduction.

NOTE: We aren't trying to make reduction fast, just create a lot of calls to substitution to compare our implementations. "Optimal reduction" is a separate problem.

Here is how we might implement full reduction using a named 
representation. i.e. where variables are represented by strings and bindings include variable names. This function recurses through terms, underneath binders looking for reduction. It defers to the `whnf` to find the leftmost reduction in an application, deferring the reduction of arguments until after they have been substituted (or after it has been determined that they won't participate in a beta-reduction.)

    nf :: Exp -> Exp
    nf (Var x) = Var x
    nf (Lam (Bind x e)) = Lam (Bind x (nf e))
       -- recursive call under the binder
    nf (App f a) =
      -- look for left-most reductions in f
      -- i.e. "weak-head normal form"
      case whnf f of
        -- Found a beta-reduction!
        Lam (Bind x b) -> nf (subst x a b)
          -- substitution needs to be careful of capture
          -- make sure that free vars of a are not captured
          -- by bound variables in b
        f' -> App (nf f') (nf a)

    -- compute weak-head normal form
    whnf :: Exp -> Exp
    whnf (Var _) = Var x
    whnf (Lam b) = Lam b
    whnf (App f a) =
      case whnf f of
        Lam (Bind x b) -> whnf (subst x a b)
        f' -> App f' a

Running example
----------------

Running example of full-reduction:

                
    λw. λx. (λy. w y (λx. w y (λx. w y))) (x x x)
            ^------------------------------------^           

Note that we need to rename two inner x variables to avoid capture. 

Using a simple, named representation, this term reduces to:
                 
                    renamed to avoid capture
                        v              v
    λw. λx. w (x x x) (λx1.w (x x x) (λx2. w (x x x)))
              ------          ------         -------
           three instances of term substituted in 
    
With *de Bruijn indices*, we would represent the same term 
as 

    λ. λ. (λ. 2 0 (λ. 3 1 (λ. 4 2))) (0 0 0)
              ^ ^     ^ ^     ^ ^ 
              indices for w & y depend on nesting level


and reduce it to 

                          shift free vars in substitutee
                          -------       -------
    λ. λ. 1 (0 0 0) (λ. 2 (1 1 1) (λ. 3 (2 2 2)))
          ^             ^             ^ 
          decrement free vars from body

With a *locally-nameless representation*, we would start with 
the same closed term (no free vars)

    λ. λ. (λ. 2 0 (λ. 3 1 (λ. 4 2))) (0 0 0)

then we would name the outermost variables before finding 
the reduct

    λw. λx. (λ. w 0 (λ. w 1 (λ. w 2))) (x x x)
            ^--------------------------------^

Now, replace substitutee with bound variable "0"

     λw. λx.

            w (x x x) (λ.w (x x x) (λ. w (x x x)))

And then close up the term, replacing free variables with 
bound variables:

     λ. λ. (λ. 2 0 (λ. 3 1 (λ. 4 2))) (0 0 0)

  
Comparing these approaches
--------------------------

Although we get the same result at the end, these three 
reduction strategies need to do extra work during what 
kinda looks to be a "linear" traversal of the term.

* With simple names, the substitution `subst x a b` needs to avoid capture. To do so, it needs to calculate the free variables of the substitutee `a` and rename any bound variables in `b` that conflict. Renaming the bound variables means that we need to find a new name that isn't free in `a`, but also isn't free in `b`. Furthermore, the set of names free at a  certain point inside `b` can change as we rename bound variables higher up.

* With de Bruin indices, the substitution needs to not just find the right place for `a`, but it also needs to shift the free variables in `a` depending on the binding depth of each new position. Furthermore, each of the free variables in `b` need to be decremented because we have now lost a binder.

      nf :: Exp -> Exp
      nf (Var x) = Var x
      nf (Lam (Bind e)) = Lam (Bind (nf e)) -- just go right under the binder
      nf (App f a) =
          case whnf f of
              Lam b -> nf (instantiate b a)   
              f' -> App (nf f') (nf a)

      -- substitute variable bound at b with a
      instantiate :: Bind Exp -> Exp -> Exp
      instantiate = ... 

* With a locally nameless representation, each time the normalization function traverses under a lambda-expression it needs to replace that bound variable (index) with a fresh free variable. This "opening" of the lambda terms means that when we substitute, there are no bound indices that need to be shifted. 

      nf' :: Exp -> N Exp                     -- run in a state monad for fresh variable gen
      nf' (Var x) = return (Var x)
      nf' (Abs b) = do 
        x <- newVar                           -- generate a fresh variable from the monad
        b' <- nf' (instantiate b (Var x))     -- bound variable substitution
        return $ Abs (close x b')
      nf' (App f a) = do
        f' <- whnf f
        case f' of
          Abs b -> do
            nf' (instantiate b a)            -- bound variable substitution
          _ -> App <$> nf' f' <*> nf' a

Head-to-head
------------

All three of these implementation strategies, if interpreted naively, are rather slow.

We can benchmark them using Lennart's term from "Lambda Calculus Cooked Four Ways". 

This term is the church encoding of: 
     
     6! == sum [1 .. 37] + 17

     i.e.  720 == 719
     i.e.  False

Statistics about this normalization
 - Number of calls to substitution required: 119,697
 - AST depth: 53
 - Binding depth: 25
 - Average # of variable occurrences in each substitution: 1.15

In the repository, the most vanilla implementations are:

- [Lennart.Simple](lib/Lennart/Simple.hs) Augustsson's implementation of the most straightforward named, capture-avoiding substitution. With a small bugfix because no one can implement this algorithm correctly the first time.

- [Lennart.DeBruijn](lib/Lennart/DeBruijn.hs) Augustsson's implementation of DeBruijn indices.

- [LocallyNameless.Ott](lib/LocallyNameless.hs) translation of the output of the locally nameless backend of the Ott tool.

(This part is mostly replicating that work, with the addition of the Locally Nameless implementation for comparison. The "fourth" way from the original paper is based on a named representation that makes use of the Barendregt variable conventions. It maintains the invariant that all bound variables are unique.)

Comparison chart
----------------

All results are available in the repository, but you'll need to look at the talk slides to see the graphs.

[results/sixteen.local/ifl_talk/nf_bench.csv](results/sixteen.local/ifl_talk/nf_bench.csv)

These results were obtained by executing the command `make normalize` when `Suite.hs` has been directed to benchmark the set `ifl_talk`.

[Next page](Part3.md)