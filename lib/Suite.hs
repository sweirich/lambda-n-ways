-- Various collections of implementations
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use :" #-}
module Suite where

import qualified Auto.Env.Strict.Env
import qualified Auto.Env.Strict.EnvGen
import qualified Auto.Env.Strict.Bind
import qualified Auto.Env.Strict.Subst
import qualified Auto.Env.Strict.EnvV
import qualified Auto.Env.Strict.EnvGenV
import qualified Auto.Env.Strict.BindV
import qualified Auto.Env.Lazy.EvalV
import qualified Auto.Env.Lazy.Env
import qualified Auto.Env.Lazy.EnvV
import qualified Auto.Env.Lazy.EnvGenV
import qualified Auto.Env.Lazy.Bind
import qualified Auto.Env.Lazy.BindV
import qualified Auto.Env.Lazy.BindVal
import qualified Auto.Env.Lazy.Subst
import qualified Auto.Env.Lazy.SubstV
import qualified Auto.Env.Lazy.ExplicitSubstV
import qualified Auto.Env.Lazy.ExplicitSubstEnvV
import qualified Auto.Manual.Strict.Env
import qualified Auto.Manual.Strict.Bind
import qualified Auto.Manual.Strict.BindV
import qualified Auto.Manual.Strict.Subst
import qualified Auto.Manual.Strict.SubstV
import qualified Auto.Manual.Strict.Eval
import qualified Auto.Manual.Lazy.Env
import qualified Auto.Manual.Lazy.EnvV
import qualified Auto.Manual.Lazy.EnvVal
import qualified Auto.Manual.Lazy.Bind
import qualified Auto.Manual.Lazy.BindV
import qualified Auto.Manual.Lazy.BindVal
import qualified Auto.Manual.Lazy.Subst
import qualified Auto.Manual.Lazy.SubstV
import qualified Auto.Manual.Lazy.Eval
import qualified Auto.Manual.Lazy.EvalV
import qualified Auto.Manual.Lazy.EnvOnlyV
import qualified Auto.Manual.Lazy.ExplicitSubstV
import qualified Auto.Manual.Lazy.ExplicitSubstEnvV
import qualified Core.Nf
import qualified DeBruijn.Bound
import qualified DeBruijn.BoundV
import qualified DeBruijn.CPDT
import qualified DeBruijn.Cornell
import qualified DeBruijn.Kit
import qualified DeBruijn.Krivine
import qualified DeBruijn.KrivineScoped
import qualified DeBruijn.Lazy.Bound
import qualified DeBruijn.Lazy.CPDT
import qualified DeBruijn.Lazy.Cornell
import qualified DeBruijn.Lazy.Kit
import qualified DeBruijn.Lazy.Lennart
import qualified DeBruijn.Lazy.Lift
import qualified DeBruijn.Lazy.Nested
import qualified DeBruijn.Lazy.Par.B
import qualified DeBruijn.Lazy.Par.Fun
import qualified DeBruijn.Lazy.Par.GB
import qualified DeBruijn.Lazy.Par.L
import qualified DeBruijn.Lazy.Par.P
import qualified DeBruijn.Lazy.Par.Scoped
import qualified DeBruijn.Lazy.TAPL
import qualified DeBruijn.Lennart
import qualified DeBruijn.Lift
import qualified DeBruijn.Nested
import qualified DeBruijn.NestedV
import qualified DeBruijn.Par.B
import qualified DeBruijn.Par.Fun
import qualified DeBruijn.Par.GB
import qualified DeBruijn.Par.L
import qualified DeBruijn.Par.P
import qualified DeBruijn.Par.Scoped
import qualified DeBruijn.TAPL
import qualified Lennart.DeBruijn
import qualified Lennart.HOAS
import qualified Lennart.Simple
import qualified Lennart.SimpleOrig
import qualified Lennart.Unique
import qualified LocallyNameless.GenericInstOpt
import qualified LocallyNameless.GenericOpt
import qualified LocallyNameless.Lazy.GenericInstOpt
import qualified LocallyNameless.Lazy.GenericOpt
import qualified LocallyNameless.Lazy.Opt
import qualified LocallyNameless.Lazy.Ott
import qualified LocallyNameless.Lazy.ParOpt
import qualified LocallyNameless.Lazy.ParScoped
import qualified LocallyNameless.Lazy.SupportOpt
import qualified LocallyNameless.Lazy.TypedOtt
import qualified LocallyNameless.Opt
import qualified LocallyNameless.Ott
import qualified LocallyNameless.ParOpt
import qualified LocallyNameless.ParScoped
import qualified LocallyNameless.SupportInstOpt
import qualified LocallyNameless.SupportOpt
import qualified LocallyNameless.TypedOpt
import qualified LocallyNameless.TypedOtt
import qualified NBE.Aelig
import qualified NBE.Boesflug
import qualified NBE.Contextual
import qualified NBE.Felgenhauer
import qualified NBE.Kovacs
import qualified NBE.KovacsNamed
import qualified NBE.Lazy.KovacsScoped
import qualified NBE.KovacsScoped
import qualified NBE.KovacsScoped2
import qualified Named.Lazy.Foil
import qualified Named.Lazy.NominalG
import qualified Named.Lazy.Simple
import qualified Named.Lazy.SimpleGH
import qualified Named.Lazy.SimpleH
import qualified Named.Lazy.SimpleM
import qualified Named.Foil
import qualified Named.FoilV
import qualified Named.Lennart
import qualified Named.NominalG
import qualified Named.Simple
import qualified Named.SimpleGH
import qualified Named.SimpleH
import qualified Named.SimpleM
import qualified Named.Unique
import qualified Unbound.UnboundGenerics
import qualified Unbound.UnboundNonGenerics
import qualified Unbound.UnboundGenericsV
import qualified Unbound.UnboundNonGenericsV
import qualified Unbound.Lazy.UnboundGenerics
import qualified Unbound.Lazy.UnboundNonGenerics
-- allow newer GHCs
--import qualified Unbound.UnboundRep
import Util.Impl (LambdaImpl)

-- | Implementations used in the benchmarking/test suite
-- RHS must be a single variable name for Makefile
impls :: [LambdaImpl]
impls = rebound_strict_envV

interleave :: [a] -> [a] -> [a]
interleave (a1 : a1s) (a2 : a2s) = a1 : a2 : interleave a1s a2s
interleave _ _ = []

broken :: [LambdaImpl]
broken =
  []



-- Implementations of normal order reduction
-- using both lazy and strict datatype definitions
-- This set generates Figure 1 of the rebound paper
rebound_comparison :: [LambdaImpl]
rebound_comparison = 
  rebound_strict ++ well_scoped_strict ++ unbound_strict

-- Well-scoped implmentations, libraries plus baseline (Kovacs)
well_scoped_strict :: [LambdaImpl]
well_scoped_strict = [ 
                NBE.KovacsScoped.impl,
                --Named.FoilV.impl, -- too slow
                Named.Foil.impl,
                DeBruijn.BoundV.impl,
                DeBruijn.Bound.impl
               ]
-- Well-scoped implmentations (unused)
well_scoped_lazy :: [LambdaImpl]
well_scoped_lazy = [ 
                NBE.Lazy.KovacsScoped.impl,
                Named.Lazy.Foil.impl,
                DeBruijn.Lazy.Nested.impl,
                DeBruijn.Lazy.Bound.impl
               ]

unbound = unbound_strict ++ unbound_lazy
rebound = rebound_strict ++ rebound_lazy

rebound_strict :: [LambdaImpl]
rebound_strict = [ 
            Auto.Env.Strict.BindV.impl,
            Auto.Env.Strict.EnvV.impl,
            Auto.Env.Strict.EnvGenV.impl, 
            Auto.Env.Strict.Bind.impl,
            Auto.Env.Strict.Env.impl,
            Auto.Env.Strict.EnvGen.impl
            ] 



rebound_lazy :: [LambdaImpl]
rebound_lazy = [ 
            Auto.Env.Lazy.BindV.impl, 
            Auto.Env.Lazy.EnvV.impl, 
            Auto.Env.Lazy.EnvGenV.impl,
            Auto.Env.Lazy.Bind.impl,
            Auto.Env.Lazy.Env.impl
            ] 


-- these versions using "substBind/instantiate" for beta-reduction
unbound_strict :: [LambdaImpl]
unbound_strict =
  [ 
    -- Unbound.UnboundGenericsV.impl, -- applicative order, not normal order
    Unbound.UnboundGenerics.impl, -- unbound-generics
    Unbound.UnboundNonGenerics.impl -- no generic programming
  ]

  -- these versions using "substBind/instantiate" for beta-reduction
unbound_lazy :: [LambdaImpl]
unbound_lazy =
  [ 
    Unbound.Lazy.UnboundGenerics.impl, -- unbound-generics
    Unbound.Lazy.UnboundNonGenerics.impl -- no generic programming
  ]

-- this is for the "environment representation benchmark"
rebound_strict_envV = [Auto.Env.Strict.EnvV.impl]

--------------------------------------------------------------------------
-- evaluation only

eval_subst = [ Auto.Manual.Lazy.BindV.impl, 
               Auto.Manual.Strict.BindV.impl]

eval_lazy = eval_manual_lazy ++ eval_auto_lazy

eval_manual_lazy = [
    --Auto.Manual.Lazy.Subst.impl, 
    --Auto.Manual.Lazy.SubstV.impl, 
    Auto.Manual.Lazy.Bind.impl,
    Auto.Manual.Lazy.BindV.impl,
    --Auto.Manual.Lazy.EvalV.impl, 
    --Auto.Manual.Lazy.EvalV.impl,
    --Auto.Manual.Lazy.EnvOnlyV.impl, -- loops
    Auto.Manual.Lazy.Env.impl,
    Auto.Manual.Lazy.EnvV.impl,
    Auto.Manual.Lazy.ExplicitSubstV.impl,
    Auto.Manual.Lazy.ExplicitSubstEnvV.impl
  ]

eval_auto_lazy = [
    -- Auto.Env.Lazy.Subst.impl, 
    -- Auto.Env.Lazy.SubstV.impl, -- much too slow
    -- Auto.Env.Lazy.Bind.impl,
    -- Auto.Env.Lazy.Eval.impl, 
    -- Auto.Env.Lazy.EvalV.impl,
    Auto.Env.Lazy.Bind.impl,
    Auto.Env.Lazy.BindV.impl,
    Auto.Env.Lazy.Env.impl, 
    Auto.Env.Lazy.EnvV.impl,
    Auto.Env.Lazy.ExplicitSubstV.impl,
    Auto.Env.Lazy.ExplicitSubstEnvV.impl
  ]


all_eval = [  Auto.Manual.Strict.Subst.impl,
             --Auto.Manual.Strict.SubstV.impl, -- runs out of memory(!)
             Auto.Manual.Strict.Bind.impl,
             Auto.Manual.Strict.BindV.impl,
             Auto.Manual.Strict.Env.impl,
             Auto.Manual.Strict.Eval.impl,
             Auto.Manual.Lazy.Subst.impl, 
             Auto.Manual.Lazy.SubstV.impl, 
             Auto.Manual.Lazy.Bind.impl,
             Auto.Manual.Lazy.BindV.impl,
             --Auto.Manual.Lazy.BindVal.impl,
             Auto.Manual.Lazy.Eval.impl, 
             Auto.Manual.Lazy.Env.impl,
             Auto.Manual.Lazy.EnvV.impl,
             --Auto.Manual.Lazy.EnvVal.impl,
             Auto.Env.Strict.Env.impl,
             Auto.Env.Strict.Bind.impl,
             Auto.Env.Strict.Subst.impl,
             Auto.Env.Lazy.EvalV.impl, 
             Auto.Env.Lazy.Env.impl,
             Auto.Env.Lazy.EnvV.impl,
             Auto.Env.Lazy.Bind.impl,
             Auto.Env.Lazy.BindV.impl,
             --Auto.Env.Lazy.BindVal.impl, 
             Auto.Env.Lazy.Subst.impl 
             -- Auto.Env.Lazy.SubstV.impl -- runs out of memory
             ] 


rebound_eval :: [LambdaImpl]
rebound_eval = [Auto.Env.Lazy.Env.impl , 
                Auto.Env.Lazy.Bind.impl ,
                Auto.Env.Lazy.Subst.impl,
                Auto.Env.Strict.Env.impl, 
                Auto.Env.Strict.Bind.impl,
                Auto.Env.Strict.Subst.impl ]
--------------------------------------------------------------------------
-- divided by implementation strategy
--
all_impls :: [LambdaImpl]
all_impls = 
  all_debruijn ++ all_locallyNameless ++ all_named ++ nbe ++ [Lennart.HOAS.impl]

all_debruijn :: [LambdaImpl]
all_debruijn = rebound -- ++ debruijn ++ debruijn_lazy ++ [Lennart.DeBruijn.impl]

all_locallyNameless :: [LambdaImpl]
all_locallyNameless = locallyNameless ++ locallyNameless_lazy

all_named :: [LambdaImpl]
all_named = named ++ lennart ++ [Lennart.Simple.impl]

--------------------------------------------------------------------------
--------------------------------------------------------------------------



-- divided by lib subdirectory

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
    DeBruijn.Par.GB.impl,
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
    DeBruijn.Lazy.Lift.impl,
    DeBruijn.Lazy.Lennart.impl,
    -- parallel substitutions
    DeBruijn.Lazy.Par.Fun.impl,
    DeBruijn.Lazy.Par.L.impl,
    DeBruijn.Lazy.Par.P.impl,
    DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Lazy.Par.GB.impl,
    -- Well-scoped single
    DeBruijn.Lazy.CPDT.impl,
    DeBruijn.Lazy.Nested.impl,
    DeBruijn.Lazy.Bound.impl, -- bound
    -- Well-scoped parallel
    DeBruijn.Lazy.Kit.impl,
    DeBruijn.Lazy.Par.Scoped.impl
  ]


-- Lennart's original implementations
lennart :: [LambdaImpl]
lennart =
  [ -- Other
    --Lennart.Unique.impl -- buggy
    --Lennart.SimpleOrig.impl -- buggy
    Lennart.Simple.impl,
    Lennart.DeBruijn.impl,
    Lennart.HOAS.impl
  ]

-- | Locally Nameless based implmentations
locallyNameless :: [LambdaImpl]
locallyNameless =
  [ LocallyNameless.Ott.impl,
    LocallyNameless.TypedOtt.impl,
    LocallyNameless.ParScoped.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.Opt.impl,
    LocallyNameless.SupportOpt.impl,
    LocallyNameless.SupportInstOpt.impl,
    LocallyNameless.GenericOpt.impl,
    LocallyNameless.GenericInstOpt.impl,
    LocallyNameless.TypedOpt.impl
  ]

locallyNameless_lazy :: [LambdaImpl]
locallyNameless_lazy =
  [ LocallyNameless.Lazy.Ott.impl,
    LocallyNameless.Lazy.TypedOtt.impl,
    LocallyNameless.Lazy.ParScoped.impl,
    LocallyNameless.Lazy.ParOpt.impl,
    LocallyNameless.Lazy.Opt.impl,
    LocallyNameless.Lazy.SupportOpt.impl,
    LocallyNameless.Lazy.GenericOpt.impl
  ]


-- | Name based/nominal implementations
named :: [LambdaImpl]
named =
  [ Named.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.SimpleM.impl,
    Named.Lennart.impl,
    Named.Simple.impl,
    Named.Unique.impl,
    Named.Foil.impl
    -- Named.Nom -- too slow
    -- Named.NominalG -- too slow
  ]

named_lazy :: [LambdaImpl]
named_lazy =
  [ Named.Lazy.SimpleH.impl,
    Named.Lazy.SimpleGH.impl,
    Named.Lazy.SimpleM.impl,
    Named.Lazy.Foil.impl
    -- Named.Lazy.NominalG -- too slow
  ]


nbe :: [LambdaImpl]
nbe =
  [ NBE.Aelig.impl,
    -- NBE.Boesflug.impl, -- hangs on full
    -- NBE.Felgenhauer.impl, -- wonky
    NBE.Kovacs.impl,
    NBE.KovacsNamed.impl,
    NBE.KovacsScoped.impl
    -- NBE.KovacsScoped2.impl
    --DeBruijn.Krivine.impl,   -- slower than the rest
    --DeBruijn.KrivineScoped.impl -- slower than the rest
  ]

---------------------------------------------------
---------------------------------------------------
-- implementations divided by source

-- implementations available on hackage
hackage :: [LambdaImpl]
hackage =
  [ -- Named.Nom.impl, -- https://hackage.haskell.org/package/nom
    -- really, really slow.
    Named.NominalG.impl, -- nominal, generally too slow (12s vs. <200 ms for everything else)
    -- https://hackage.haskell.org/package/nominal
    Named.Lazy.NominalG.impl,
    -- Unbound.UnboundRep.impl, -- unbound
    Unbound.UnboundGenerics.impl, -- unbound-generics
    DeBruijn.Bound.impl, -- bound
    DeBruijn.Lazy.Bound.impl, -- bound
    Named.Foil.impl,
    Named.Lazy.Foil.impl -- free-foil
  ]

---------------------------------------------------
---------------------------------------------------
-- those that use generic programming somehow

generic :: [LambdaImpl]
generic =
  [ DeBruijn.Par.GB.impl,
    DeBruijn.Lazy.Par.GB.impl,
    LocallyNameless.GenericOpt.impl,
    LocallyNameless.Lazy.GenericOpt.impl,
    Named.SimpleGH.impl
  ]

---------------------------------------------------
---------------------------------------------------
-- same implementations, roughly divided by speed

fast :: [LambdaImpl]
fast =
  [ Lennart.HOAS.impl,
    LocallyNameless.Opt.impl,
    LocallyNameless.Lazy.Opt.impl,
    LocallyNameless.SupportInstOpt.impl,
    LocallyNameless.GenericInstOpt.impl,
    LocallyNameless.ParOpt.impl,
    LocallyNameless.Lazy.ParOpt.impl,
    DeBruijn.Par.Scoped.impl,
    DeBruijn.Lazy.Par.Scoped.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Par.GB.impl,
    DeBruijn.Lazy.Par.GB.impl,
    DeBruijn.Bound.impl,
    DeBruijn.Lazy.Bound.impl,
    Named.SimpleH.impl,
    Named.Lazy.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.Lazy.SimpleGH.impl,
    Named.Foil.impl,
    Auto.Env.Lazy.Bind.impl,
    Auto.Manual.Lazy.Env.impl
  ]

-- fastest implementation in each category in the NF benchmark
fast_nf :: [LambdaImpl]
fast_nf = rebound ++ nbe 
   ++ [ Auto.Manual.Lazy.Env.impl, Auto.Manual.Strict.Env.impl ]
{-  [ -- LocallyNameless.Opt.impl, -- 2.56 XXX
    -- LocallyNameless.SupportOpt.impl, -- 2.59  -- new version of GHC degraded performance
    DeBruijn.Par.Scoped.impl, -- 3.00
    -- LocallyNameless.GenericOpt.impl, -- 4.36    -- new version of GHC degraded performance
    --	LocallyNameless.TypedOpt.impl, -- 3.27
    DeBruijn.Lazy.Par.Scoped.impl, -- 5.35
    DeBruijn.Bound.impl, -- 6.07
    DeBruijn.Par.B.impl, -- 7.43
    LocallyNameless.ParOpt.impl, -- 7.46
    DeBruijn.Par.GB.impl, -- 8.51
    DeBruijn.Lazy.Par.GB.impl, -- 11.4
    DeBruijn.Lazy.Par.B.impl, -- 13
    DeBruijn.Lazy.Bound.impl, -- 13.09
    Lennart.HOAS.impl -- 17.4
    -- Named.SimpleH.impl, -- 122
    -- Named.Lazy.SimpleH.impl, -- 166
    -- Named.Lazy.SimpleGH.impl, -- 169
    -- Named.SimpleGH.impl -- 193
  ] -}

fast_random :: [LambdaImpl]
fast_random =
  [ Lennart.HOAS.impl, -- 1
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

fast_debruijn :: [LambdaImpl]
fast_debruijn =
  [ DeBruijn.Par.B.impl,
    --DeBruijn.Par.FB.impl,
    DeBruijn.Bound.impl, -- bound
    DeBruijn.Nested.impl
  ]

fast_debruijn_lazy :: [LambdaImpl]
fast_debruijn_lazy =
  [ DeBruijn.Lazy.Par.B.impl,
    --DeBruijn.Lazy.Par.FB.impl,
    DeBruijn.Lazy.Bound.impl, -- bound
    DeBruijn.Lazy.Nested.impl
  ]

fast_locally_nameless :: [LambdaImpl]
fast_locally_nameless =
  [ LocallyNameless.Opt.impl,
    LocallyNameless.ParOpt.impl
    --    LocallyNameless.TypedOpt.impl,
  ]

fast_named :: [LambdaImpl]
fast_named =
  [ Named.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.SimpleM.impl
  ]

slow :: [LambdaImpl]
slow =
  [ DeBruijn.Par.L.impl,
    DeBruijn.Par.Fun.impl,
    DeBruijn.Par.P.impl,
    LocallyNameless.ParScoped.impl,
    --    LocallyNameless.TypedOtt.impl,
    Named.Simple.impl,
    Named.Unique.impl
  ]

really_slow :: [LambdaImpl]
really_slow = [Named.NominalG.impl] -- nominal

--------------------------------------------------------------
--------------------------------------------------------------
-- Versions discussed in the Haskell.love talk Sept 2021

love_talk :: [LambdaImpl]
love_talk = basic_lazy ++ basic_strict ++ opt_lazy ++ opt_strict ++ opt_lazy_generic ++ opt_strict_generic

basic_lazy :: [LambdaImpl]
basic_lazy =
  [ -- Lennart.SimpleOrig.impl,
    Lennart.Simple.impl,
    Lennart.DeBruijn.impl,
    LocallyNameless.Lazy.Ott.impl
  ]

basic_strict :: [LambdaImpl]
basic_strict =
  [ Named.Lennart.impl,
    -- Named.Simple.impl,
    DeBruijn.Lennart.impl,
    LocallyNameless.Ott.impl
  ]

opt_strict :: [LambdaImpl]
opt_strict =
  [ Named.SimpleH.impl,
    DeBruijn.Par.B.impl,
    LocallyNameless.Opt.impl
  ]

opt_lazy :: [LambdaImpl]
opt_lazy =
  [ Named.Lazy.SimpleH.impl,
    DeBruijn.Lazy.Par.B.impl,
    LocallyNameless.Lazy.Opt.impl
  ]

opt_strict_generic :: [LambdaImpl]
opt_strict_generic =
  [ Named.SimpleGH.impl,
    DeBruijn.Par.GB.impl,
    LocallyNameless.GenericInstOpt.impl
  ]

opt_lazy_generic :: [LambdaImpl]
opt_lazy_generic =
  [ Named.Lazy.SimpleGH.impl,
    DeBruijn.Lazy.Par.GB.impl,
    LocallyNameless.Lazy.GenericInstOpt.impl
  ]

love_all :: [LambdaImpl]
love_all =
  [ Lennart.Simple.impl,
    Named.Lennart.impl,
    Named.SimpleH.impl,
    Named.Lazy.SimpleH.impl,
    Named.SimpleGH.impl,
    Named.Lazy.SimpleGH.impl,
    Lennart.DeBruijn.impl,
    DeBruijn.Lennart.impl,
    DeBruijn.Par.B.impl,
    DeBruijn.Lazy.Par.B.impl,
    DeBruijn.Par.GB.impl,
    DeBruijn.Lazy.Par.GB.impl,
    LocallyNameless.Lazy.Ott.impl,
    LocallyNameless.Ott.impl,
    LocallyNameless.Opt.impl,
    LocallyNameless.Lazy.Opt.impl,
    LocallyNameless.GenericInstOpt.impl,
    LocallyNameless.Lazy.GenericInstOpt.impl
  ]
