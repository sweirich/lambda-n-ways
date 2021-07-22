module Suite where

import qualified Core.Nf
import qualified DeBruijn.Bound
import qualified DeBruijn.Chlipala
import qualified DeBruijn.Cornell
import qualified DeBruijn.Kit
import qualified DeBruijn.Lennart
import qualified DeBruijn.Lift
import qualified DeBruijn.List
import qualified DeBruijn.Nested
import qualified DeBruijn.Nested2
import qualified DeBruijn.Par.B
import qualified DeBruijn.Par.F
import qualified DeBruijn.Par.FB
import qualified DeBruijn.Par.L
import qualified DeBruijn.Par.P
import qualified DeBruijn.Par.Scoped
import Impl (LambdaImpl)
import qualified Lambda
import qualified Lennart.HOAS
import qualified Lennart.Simple
import qualified Lennart.Unique
import qualified LocallyNameless.Opt
import qualified LocallyNameless.Ott
import qualified LocallyNameless.Par
import qualified LocallyNameless.ParOpt
import qualified LocallyNameless.Typed
import qualified LocallyNameless.TypedOpt
import qualified LocallyNameless.Unbound
import qualified LocallyNameless.UnboundGenerics
-- import qualified Named.Nom
import qualified Named.Nominal
import qualified Named.NominalG
import qualified Named.SimpleB
import qualified Named.SimpleH
import qualified Named.SimpleM

-- | Implementations used in the benchmarking/test suite
impls :: [LambdaImpl]
impls = fast_impls

--------------------------------------------------------------------------
--------------------------------------------------------------------------
-- divided by implementation strategy
--

all_impls :: [LambdaImpl]
all_impls =
  debruijn ++ locallyNameless ++ named ++ other

-- | deBruijn index-based implementations
debruijn :: [LambdaImpl]
debruijn =
  [ DeBruijn.Lennart.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Par.F.impl,
    DeBruijn.Par.FB.impl,
    DeBruijn.Par.L.impl,
    DeBruijn.Par.P.impl,
    DeBruijn.Par.Scoped.impl,
    DeBruijn.Bound.impl,
    DeBruijn.Chlipala.impl,
    DeBruijn.Cornell.impl,
    DeBruijn.Kit.impl,
    DeBruijn.Lift.impl,
    DeBruijn.List.impl,
    DeBruijn.Nested.impl
    -- DeBruijn.Nested2.impl, --fails test suite
  ]

-- | Locally Nameless based implmentations
locallyNameless :: [LambdaImpl]
locallyNameless =
  [ LocallyNameless.Opt.impl,
    LocallyNameless.Ott.impl,
    LocallyNameless.Par.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.Typed.impl,
    LocallyNameless.TypedOpt.impl,
    LocallyNameless.Unbound.impl, -- unbound
    LocallyNameless.UnboundGenerics.impl -- unbound-generics
  ]

-- | Name based/nominal implementations
named :: [LambdaImpl]
named =
  [ -- Named.Nom.impl, doesn't compile
    -- Named.Nominal.impl, -- fails test suite
    Named.NominalG.impl, -- generally too slow (12s vs. <200 ms for everything else)
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

fast_impls :: [LambdaImpl]
fast_impls =
  fast_debruijn ++ fast_locally_nameless ++ fast_named
    ++ other

fast_debruijn :: [LambdaImpl]
fast_debruijn =
  [ DeBruijn.Lennart.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Par.FB.impl,
    DeBruijn.Par.Scoped.impl,
    DeBruijn.Bound.impl,
    DeBruijn.Chlipala.impl,
    DeBruijn.Cornell.impl,
    DeBruijn.Kit.impl,
    DeBruijn.Lift.impl,
    DeBruijn.List.impl,
    DeBruijn.Nested.impl
  ]

fast_locally_nameless :: [LambdaImpl]
fast_locally_nameless =
  [ LocallyNameless.Opt.impl,
    LocallyNameless.Ott.impl,
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
    DeBruijn.Par.F.impl,
    DeBruijn.Par.P.impl,
    LocallyNameless.Par.impl,
    LocallyNameless.Typed.impl,
    LocallyNameless.Unbound.impl, -- unbound
    Lennart.Simple.impl,
    Lennart.Unique.impl
  ]

really_slow :: [LambdaImpl]
really_slow = [Named.NominalG.impl]

--------------------------------------------------------------
--------------------------------------------------------------
