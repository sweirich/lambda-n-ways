Related work
------------

This project was inspired by Lennart Augustsson's "Lambda Calculus Four Ways" as well as a number of existing binding libraries.

* Cheney - FreshLib (names)
* Weirich and Yorgey - Unbound (locally nameless)
* Modern version of unbound: unbound-generics by Aleksey Kliger
* Kmett - Bound  (de Bruijn indices)


Conclusion and Future work
---------------------------

What you have seen:
 - Three new binding libraries that you can use today in your code. 
    + All have similar, but not the same interface.
    + All support multiple variable sorts (e.g. System F)
    + None support pattern binding
    + Strongly-typed variant for de Bruijn version also available

 - Platform for testing and benchmarking existing approaches and libraries
    + Many more implementations included in benchmarks
    + Other benchmarks: normalization for other lambda terms,
         alpha-equality, conversion to/from named representation
    + Send me pull requests for new implementations 

Future work:
- Publish these three libraries as a separate Haskell package
- Generalize to pattern binding
- Update unbound-generics with these ideas



