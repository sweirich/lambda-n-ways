module Suite where

import qualified Core.Nf
import qualified DeBruijn.Bound
import qualified DeBruijn.CPDT
import qualified DeBruijn.Cornell
import qualified DeBruijn.Kit
import qualified DeBruijn.Lazy.Bound
import qualified DeBruijn.Lazy.CPDT
import qualified DeBruijn.Lazy.Cornell
import qualified DeBruijn.Lazy.Kit
import qualified DeBruijn.Lazy.Lennart
import qualified DeBruijn.Lazy.Lift
import qualified DeBruijn.Lazy.List
import qualified DeBruijn.Lazy.Nested
--import qualified DeBruijn.Nested2
import qualified DeBruijn.Lazy.Par.B
import qualified DeBruijn.Lazy.Par.FB
import qualified DeBruijn.Lazy.Par.Fun
import qualified DeBruijn.Lazy.Par.L
import qualified DeBruijn.Lazy.Par.P
import qualified DeBruijn.Lazy.Par.Scoped
import qualified DeBruijn.Lazy.TAPL
import qualified DeBruijn.Lennart
import qualified DeBruijn.Lift
import qualified DeBruijn.List
import qualified DeBruijn.Nested
-- import qualified DeBruijn.Nested2
import qualified DeBruijn.Par.B
import qualified DeBruijn.Par.FB
import qualified DeBruijn.Par.Fun
import qualified DeBruijn.Par.L
import qualified DeBruijn.Par.P
import qualified DeBruijn.Par.Scoped
import qualified DeBruijn.TAPL
import qualified Lennart.HOAS
import qualified Lennart.Simple
import qualified Lennart.Unique
import qualified LocallyNameless.Opt
import qualified LocallyNameless.Ott
import qualified LocallyNameless.ParOpt
import qualified LocallyNameless.ParScoped
import qualified LocallyNameless.TypedOpt
import qualified LocallyNameless.TypedOtt
import qualified LocallyNameless.Lazy.Opt
import qualified LocallyNameless.Lazy.Ott
import qualified LocallyNameless.Lazy.ParOpt
import qualified LocallyNameless.Lazy.ParScoped
import qualified LocallyNameless.Lazy.TypedOpt
import qualified LocallyNameless.Lazy.TypedOtt
import qualified LocallyNameless.UnboundGenerics
import qualified LocallyNameless.UnboundRep
-- import qualified Named.Nom
--import qualified Named.Nominal
import qualified Named.NominalG
--import qualified Named.SimpleB
import qualified Named.SimpleH
import qualified Named.SimpleM
import Util.Impl (LambdaImpl)

-- | Implementations used in the benchmarking/test suite
impls :: [LambdaImpl]
impls = fast_random

interleave :: [a] -> [a] -> [a]
interleave (a1 : a1s) (a2 : a2s) = a1 : a2 : interleave a1s a2s
interleave _ _ = []

--------------------------------------------------------------------------
--------------------------------------------------------------------------
-- divided by implementation strategy
--

all_impls :: [LambdaImpl]
all_impls =
  debruijn ++ debruijn_lazy ++ locallyNameless ++ named ++ other

-- | deBruijn index-based implementations
debruijn :: [LambdaImpl]
debruijn =
  [ -- single substitutions
    DeBruijn.TAPL.impl,
    DeBruijn.List.impl,
    DeBruijn.Lennart.impl,
    DeBruijn.Cornell.impl,
    DeBruijn.Lift.impl,
    -- parallel substitutions
    DeBruijn.Par.B.impl,
    DeBruijn.Par.FB.impl,
    DeBruijn.Par.P.impl,
    DeBruijn.Par.Fun.impl,
    DeBruijn.Par.L.impl,
    -- Well-scoped
    DeBruijn.Par.Scoped.impl,
    DeBruijn.Bound.impl, -- bound
    DeBruijn.Nested.impl,
    DeBruijn.CPDT.impl,
    DeBruijn.Kit.impl
    -- DeBruijn.Nested2.impl, --fails test suite
  ]

debruijn_lazy :: [LambdaImpl]
debruijn_lazy =
  [ -- single substitutions
    DeBruijn.Lazy.TAPL.impl,
    DeBruijn.Lazy.List.impl,
    DeBruijn.Lazy.Lennart.impl,
    DeBruijn.Lazy.Cornell.impl,
    DeBruijn.Lazy.Lift.impl,
    -- parallel substitutions
    DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Lazy.Par.FB.impl,
    DeBruijn.Lazy.Par.P.impl,
    DeBruijn.Lazy.Par.Fun.impl,
    DeBruijn.Lazy.Par.L.impl,
    -- Well-scoped
    DeBruijn.Lazy.Par.Scoped.impl,
    DeBruijn.Lazy.Bound.impl, -- bound
    DeBruijn.Lazy.Nested.impl,
    DeBruijn.Lazy.CPDT.impl,
    DeBruijn.Lazy.Kit.impl
  ]

-- | Locally Nameless based implmentations
locallyNameless :: [LambdaImpl]
locallyNameless =
  [ LocallyNameless.Opt.impl,
    LocallyNameless.Ott.impl,
    LocallyNameless.ParScoped.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.TypedOtt.impl,
    LocallyNameless.TypedOpt.impl,
    LocallyNameless.UnboundRep.impl, -- unbound
    LocallyNameless.UnboundGenerics.impl -- unbound-generics
  ]

-- | Name based/nominal implementations
named :: [LambdaImpl]
named =
  [ -- Named.Nom.impl, doesn't compile
    -- Named.Nominal.impl, -- fails test suite
    Named.NominalG.impl, -- nominal, generally too slow (12s vs. <200 ms for everything else)
    -- Named.SimpleB.impl, -- fails test suite
    Named.SimpleH.impl,
    Named.SimpleM.impl
  ]

other :: [LambdaImpl]
other =
  [ -- Other
    Lennart.HOAS.impl,
    Core.Nf.impl
  ]

---------------------------------------------------
---------------------------------------------------
-- same implementations, roughly divided by speed

-- fastest implementation in each category in the NF benchmark
fast_nf :: [LambdaImpl]
fast_nf = [
        LocallyNameless.Opt.impl, -- 2.81
	DeBruijn.Par.Scoped.impl, -- 2.93
	LocallyNameless.TypedOpt.impl, -- 3.27
	DeBruijn.Lazy.Par.Scoped.impl, -- 5.2
	DeBruijn.Par.B.impl, -- 5.31
	LocallyNameless.ParOpt.impl, -- 6.13
	DeBruijn.Bound.impl, -- 7.18
	DeBruijn.Lazy.Par.B.impl, -- 9.55
	Lennart.HOAS.impl, -- 17.4
	Named.SimpleH.impl -- 108
	]

fast_random :: [LambdaImpl]
fast_random = [
	Lennart.HOAS.impl, -- 1
        LocallyNameless.Opt.impl, -- 254 -- 264
	DeBruijn.Lazy.Par.Scoped.impl, -- 269 -- 261
        LocallyNameless.TypedOpt.impl, -- 325 -- 327			
	DeBruijn.Lazy.Par.B.impl, -- 356 -- 344
	LocallyNameless.ParOpt.impl, -- 678 -- 684
	DeBruijn.Par.Scoped.impl, -- 876 -- 1360 
	DeBruijn.Par.B.impl, -- 954 -- 1310
	Named.SimpleH.impl, -- 7780 -- 11200
	DeBruijn.Bound.impl -- 8440 -- 9500
        ] 

-- Fast implementations overall
fast_impls :: [LambdaImpl]
fast_impls =
  fast_debruijn ++ fast_debruijn_lazy ++ fast_locally_nameless ++ fast_named
    ++ other

fast_debruijn :: [LambdaImpl]
fast_debruijn =
  [ DeBruijn.Par.B.impl,
    DeBruijn.Par.FB.impl,
    DeBruijn.Bound.impl, -- bound
    DeBruijn.Nested.impl
  ]

fast_debruijn_lazy :: [LambdaImpl]
fast_debruijn_lazy =
  [ DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Lazy.Par.FB.impl,
    DeBruijn.Lazy.Bound.impl, -- bound
    DeBruijn.Lazy.Nested.impl
  ]

fast_locally_nameless :: [LambdaImpl]
fast_locally_nameless =
  [ LocallyNameless.Opt.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.TypedOpt.impl,
    LocallyNameless.UnboundGenerics.impl -- unbound-generics
  ]

fast_named :: [LambdaImpl]
fast_named =
  [ Named.SimpleH.impl,
    Named.SimpleM.impl
  ]

slow :: [LambdaImpl]
slow =
  [ DeBruijn.Par.L.impl,
    DeBruijn.Par.Fun.impl,
    DeBruijn.Par.P.impl,
    LocallyNameless.ParScoped.impl,
    LocallyNameless.TypedOtt.impl,
    LocallyNameless.UnboundRep.impl, -- unbound
    Lennart.Simple.impl,
    Lennart.Unique.impl
  ]

really_slow :: [LambdaImpl]
really_slow = [Named.NominalG.impl] -- nominal

--------------------------------------------------------------
--------------------------------------------------------------
