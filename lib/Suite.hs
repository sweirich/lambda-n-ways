module Suite where

import qualified Core.Nf
import qualified Lennart.HOAS

import qualified DeBruijn.Bound
import qualified DeBruijn.CPDT
import qualified DeBruijn.Cornell
import qualified DeBruijn.Kit
import qualified DeBruijn.Lennart
import qualified DeBruijn.Lift
import qualified DeBruijn.List
import qualified DeBruijn.Nested
import qualified DeBruijn.Par.B
import qualified DeBruijn.Par.FB
import qualified DeBruijn.Par.Fun
import qualified DeBruijn.Par.L
import qualified DeBruijn.Par.P
import qualified DeBruijn.Par.Scoped
import qualified DeBruijn.TAPL
import qualified DeBruijn.Lazy.Bound
import qualified DeBruijn.Lazy.CPDT
import qualified DeBruijn.Lazy.Cornell
import qualified DeBruijn.Lazy.Kit
import qualified DeBruijn.Lazy.Lennart
import qualified DeBruijn.Lazy.Lift
import qualified DeBruijn.Lazy.List
import qualified DeBruijn.Lazy.Nested
import qualified DeBruijn.Lazy.Par.B
import qualified DeBruijn.Lazy.Par.FB
import qualified DeBruijn.Lazy.Par.Fun
import qualified DeBruijn.Lazy.Par.L
import qualified DeBruijn.Lazy.Par.P
import qualified DeBruijn.Lazy.Par.Scoped
import qualified DeBruijn.Lazy.TAPL

import qualified LocallyNameless.Opt
import qualified LocallyNameless.Ott
import qualified LocallyNameless.ParOpt
import qualified LocallyNameless.ParScoped
--import qualified LocallyNameless.TypedOpt
import qualified LocallyNameless.TypedOtt
import qualified LocallyNameless.UnboundGenerics
import qualified LocallyNameless.UnboundRep
import qualified LocallyNameless.UGSubstBind
import qualified LocallyNameless.Lazy.Opt
import qualified LocallyNameless.Lazy.Ott
import qualified LocallyNameless.Lazy.ParOpt
import qualified LocallyNameless.Lazy.ParScoped
--import qualified LocallyNameless.Lazy.TypedOpt
import qualified LocallyNameless.Lazy.TypedOtt
import qualified LocallyNameless.Lazy.UnboundGenerics
import qualified LocallyNameless.Lazy.UnboundRep
import qualified LocallyNameless.Lazy.UGSubstBind

import qualified Named.NominalG
import qualified Named.SimpleH
import qualified Named.SimpleM
import qualified Named.Simple
import qualified Named.Unique
import Util.Impl (LambdaImpl)

-- | Implementations used in the benchmarking/test suite
impls :: [LambdaImpl]
impls = all_impls


interleave :: [a] -> [a] -> [a]
interleave (a1 : a1s) (a2 : a2s) = a1 : a2 : interleave a1s a2s
interleave _ _ = []

--------------------------------------------------------------------------
--------------------------------------------------------------------------
-- divided by implementation strategy
--

all_impls :: [LambdaImpl]
all_impls =
  debruijn ++ debruijn_lazy ++ locallyNameless ++ locallyNameless_lazy ++ named ++ other

-- | deBruijn index-based implementations
debruijn :: [LambdaImpl]
debruijn =
  [ -- single substitutions
    DeBruijn.TAPL.impl,
    DeBruijn.Cornell.impl,
    DeBruijn.Lennart.impl,
    DeBruijn.Lift.impl,
    -- parallel substitutions
    DeBruijn.Par.L.impl,
    DeBruijn.Par.Fun.impl,
    DeBruijn.Par.P.impl,
    DeBruijn.Par.B.impl,
    -- Well-scoped single
    DeBruijn.CPDT.impl,
    DeBruijn.Nested.impl,
    DeBruijn.Bound.impl, -- bound
    -- well-scoped parallel
    DeBruijn.Kit.impl,
    DeBruijn.Par.Scoped.impl
    -- DeBruijn.Nested2.impl, --fails test suite
  ]

debruijn_lazy :: [LambdaImpl]
debruijn_lazy =
  [ -- single substitutions
    DeBruijn.Lazy.TAPL.impl,
    DeBruijn.Lazy.Cornell.impl,
    DeBruijn.Lazy.Lennart.impl,
    DeBruijn.Lazy.Lift.impl,
    -- parallel substitutions
    DeBruijn.Lazy.Par.L.impl,
    DeBruijn.Lazy.Par.Fun.impl,
    DeBruijn.Lazy.Par.P.impl,
    DeBruijn.Lazy.Par.B.impl,
    -- Well-scoped single
    DeBruijn.Lazy.CPDT.impl,
    DeBruijn.Lazy.Nested.impl,
    DeBruijn.Lazy.Bound.impl, -- bound
    -- Well-scoped parallel
    DeBruijn.Lazy.Kit.impl,
    DeBruijn.Lazy.Par.Scoped.impl
  ]

-- | Locally Nameless based implmentations
locallyNameless :: [LambdaImpl]
locallyNameless =
  [ 
    LocallyNameless.Ott.impl,
    LocallyNameless.TypedOtt.impl,
    LocallyNameless.ParScoped.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.Opt.impl,
    -- LocallyNameless.TypedOpt.impl,
    LocallyNameless.UnboundRep.impl, -- unbound
    LocallyNameless.UnboundGenerics.impl, -- unbound-generics mod1
    LocallyNameless.UGSubstBind.impl -- unbound-generics mod2
  ]

locallyNameless_lazy :: [LambdaImpl]
locallyNameless_lazy =
  [ 
    LocallyNameless.Lazy.Ott.impl,
    LocallyNameless.Lazy.TypedOtt.impl,
    LocallyNameless.Lazy.ParScoped.impl,
    LocallyNameless.Lazy.ParOpt.impl,
    LocallyNameless.Lazy.Opt.impl,
    -- LocallyNameless.Lazy.TypedOpt.impl,
    LocallyNameless.Lazy.UnboundRep.impl, -- unbound
    LocallyNameless.Lazy.UnboundGenerics.impl, -- unbound-generics
    LocallyNameless.Lazy.UGSubstBind.impl
  ]


-- | Name based/nominal implementations
named :: [LambdaImpl]
named =
  [ -- Named.Nom.impl, doesn't compile
    -- Named.Nominal.impl, -- fails test suite
    Named.NominalG.impl, -- nominal, generally too slow (12s vs. <200 ms for everything else)
    -- Named.SimpleB.impl, -- fails test suite
    Named.SimpleH.impl,
    Named.SimpleM.impl,
    Named.Simple.impl,
    Named.Unique.impl
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
--	LocallyNameless.TypedOpt.impl, -- 3.27
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
	LocallyNameless.Lazy.Opt.impl, -- 363 -- 178
        LocallyNameless.Opt.impl, -- 434 -- 264
	DeBruijn.Lazy.Par.Scoped.impl, -- 269 -- 261
--        LocallyNameless.Lazy.TypedOpt.impl, -- 312 -- 316
--        LocallyNameless.TypedOpt.impl, -- 321 -- 327			
	DeBruijn.Lazy.Par.B.impl, -- 356 -- 344
	LocallyNameless.Lazy.ParOpt.impl, -- 557 -- 546
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
--    LocallyNameless.TypedOpt.impl,
    LocallyNameless.UGSubstBind.impl,
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
--    LocallyNameless.TypedOtt.impl,
    LocallyNameless.UnboundRep.impl, -- unbound
    Named.Simple.impl,
    Named.Unique.impl
  ]

really_slow :: [LambdaImpl]
really_slow = [Named.NominalG.impl] -- nominal

--------------------------------------------------------------
--------------------------------------------------------------
