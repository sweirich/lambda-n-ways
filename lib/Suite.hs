module Suite(impls) where

import Lambda
import IdInt
import Impl

import Simple
import SimpleB
import Unique
import HOAS
import DeBruijn
-- import DeBruijnC
import DeBruijnParF
import DeBruijnParB
import BoundDB
import Unbound
import UnboundGenerics
import DeBruijnScoped
import Core.Nf

import Test.QuickCheck

impls :: [LambdaImpl]
impls = [ DeBruijnParB.impl
        , DeBruijnScoped.impl
        , BoundDB.impl
        , HOAS.impl
        , SimpleB.impl
        , DeBruijnParF.impl
        , Simple.impl 
        , DeBruijn.impl
        , UnboundGenerics.impl 
        , Unbound.impl
        , Unique.impl
        , Core.Nf.impl
        ]
