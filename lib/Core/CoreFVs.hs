{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

Taken quite directly from the Peyton Jones/Lester paper.
-}
{-# LANGUAGE CPP #-}

-- | A module concerned with finding the free variables of an expression.
module Core.CoreFVs
  ( -- * Free variables of expressions and binding groups
    exprFreeVars,
    --exprFreeVarsDSet,
    exprFreeVarsList,
    exprFreeIds,
    --exprFreeIdsDSet,
    exprFreeIdsList,
    --exprsFreeIdsDSet,
    exprsFreeIdsList,
    exprsFreeVars,
    exprsFreeVarsList,
    --bindFreeVars,

    -- * Selective free variables of expressions
    InterestingVarFun,
    exprSomeFreeVars,
    exprsSomeFreeVars,
    exprSomeFreeVarsList,
    exprsSomeFreeVarsList,

    -- * Free variables of Rules, Vars and Ids

    --idFreeVars, dIdFreeVars,
    --idFVs,

    expr_fvs,
    {-
    -- * Core syntax tree annotation with free variables
    FVAnn,                  -- annotation, abstract
    CoreExprWithFVs,        -- = AnnExpr Id FVAnn
    CoreExprWithFVs',       -- = AnnExpr' Id FVAnn
    CoreBindWithFVs,        -- = AnnBind Id FVAnn
    CoreAltWithFVs,         -- = AnnAlt Id FVAnn
    freeVars,               -- CoreExpr -> CoreExprWithFVs
    freeVarsBind,           -- CoreBind -> DVarSet -> (DVarSet, CoreBindWithFVs)
    freeVarsOf,             -- CoreExprWithFVs -> DIdSet
    freeVarsOfAnn
    -}
  )
where

import Core.Core
import Core.FV as FV
import Core.VarSet
import qualified Util.Syntax.Lambda as LC

{-
import GHC.Prelude

import GHC.Core
import GHC.Types.Id
import GHC.Types.Id.Info
import GHC.Types.Name.Set
import GHC.Types.Unique.Set
import GHC.Types.Unique (Uniquable (..))
import GHC.Types.Name
import GHC.Types.Var.Set
import GHC.Types.Var
import GHC.Core.Type
import GHC.Core.TyCo.Rep
import GHC.Core.TyCo.FVs
import GHC.Core.TyCon
import GHC.Core.Coercion.Axiom
import GHC.Core.FamInstEnv
import GHC.Builtin.Types.Prim( funTyConName )
import GHC.Data.Maybe( orElse )
import GHC.Utils.Misc
import GHC.Types.Basic( Activation )
import GHC.Utils.Outputable
import GHC.Utils.FV as FV
-}

{-
************************************************************************
*                                                                      *
\section{Finding the free variables of an expression}
*                                                                      *
************************************************************************

This function simply finds the free variables of an expression.
So far as type variables are concerned, it only finds tyvars that are

        * free in type arguments,
        * free in the type of a binder,

but not those that are free in the type of variable occurrence.
-}

-- | Find all locally-defined free Ids or type variables in an expression
-- returning a non-deterministic set.
exprFreeVars :: CoreExpr -> VarSet
exprFreeVars = fvVarSet . exprFVs

-- | Find all locally-defined free Ids or type variables in an expression
-- returning a composable FV computation. See Note [FV naming conventions] in GHC.Utils.FV
-- for why export it.
exprFVs :: CoreExpr -> FV
exprFVs = filterFV isLocalVar . expr_fvs

-- | Find all locally-defined free Ids or type variables in an expression
-- returning a deterministic set.
-- exprFreeVarsDSet :: CoreExpr -> DVarSet
-- exprFreeVarsDSet = fvDVarSet . exprFVs

-- | Find all locally-defined free Ids or type variables in an expression
-- returning a deterministically ordered list.
exprFreeVarsList :: CoreExpr -> [Var]
exprFreeVarsList = fvVarList . exprFVs

-- | Find all locally-defined free Ids in an expression
exprFreeIds :: CoreExpr -> IdSet -- Find all locally-defined free Ids
exprFreeIds = exprSomeFreeVars isLocalId

-- | Find all locally-defined free Ids in an expression
-- returning a deterministic set.
-- exprFreeIdsDSet :: CoreExpr -> DIdSet -- Find all locally-defined free Ids
-- exprFreeIdsDSet = exprSomeFreeVarsDSet isLocalId

-- | Find all locally-defined free Ids in an expression
-- returning a deterministically ordered list.
exprFreeIdsList :: CoreExpr -> [Id] -- Find all locally-defined free Ids
exprFreeIdsList = exprSomeFreeVarsList isLocalId

-- | Find all locally-defined free Ids in several expressions
-- returning a deterministic set.
-- exprsFreeIdsDSet :: [CoreExpr] -> DIdSet -- Find all locally-defined free Ids
-- exprsFreeIdsDSet = exprsSomeFreeVarsDSet isLocalId

-- | Find all locally-defined free Ids in several expressions
-- returning a deterministically ordered list.
exprsFreeIdsList :: [CoreExpr] -> [Id] -- Find all locally-defined free Ids
exprsFreeIdsList = exprsSomeFreeVarsList isLocalId

-- | Find all locally-defined free Ids or type variables in several expressions
-- returning a non-deterministic set.
exprsFreeVars :: [CoreExpr] -> VarSet
exprsFreeVars = fvVarSet . exprsFVs

-- | Find all locally-defined free Ids or type variables in several expressions
-- returning a composable FV computation. See Note [FV naming conventions] in GHC.Utils.FV
-- for why export it.
exprsFVs :: [CoreExpr] -> FV
exprsFVs exprs = mapUnionFV exprFVs exprs

-- | Find all locally-defined free Ids or type variables in several expressions
-- returning a deterministically ordered list.
exprsFreeVarsList :: [CoreExpr] -> [Var]
exprsFreeVarsList = fvVarList . exprsFVs

-- | Finds free variables in an expression selected by a predicate
exprSomeFreeVars ::
  -- | Says which 'Var's are interesting
  InterestingVarFun ->
  CoreExpr ->
  VarSet
exprSomeFreeVars fv_cand e = fvVarSet $ filterFV fv_cand $ expr_fvs e

-- | Finds free variables in an expression selected by a predicate
-- returning a deterministically ordered list.
exprSomeFreeVarsList ::
  -- | Says which 'Var's are interesting
  InterestingVarFun ->
  CoreExpr ->
  [Var]
exprSomeFreeVarsList fv_cand e = fvVarList $ filterFV fv_cand $ expr_fvs e

-- | Finds free variables in an expression selected by a predicate
-- returning a deterministic set.

{-
exprSomeFreeVarsDSet :: InterestingVarFun -- ^ Says which 'Var's are interesting
                     -> CoreExpr
                     -> DVarSet
exprSomeFreeVarsDSet fv_cand e = fvDVarSet $ filterFV fv_cand $ expr_fvs e
-}

-- | Finds free variables in several expressions selected by a predicate
exprsSomeFreeVars ::
  InterestingVarFun -> -- Says which 'Var's are interesting
  [CoreExpr] ->
  VarSet
exprsSomeFreeVars fv_cand es =
  fvVarSet $ filterFV fv_cand $ mapUnionFV expr_fvs es

-- | Finds free variables in several expressions selected by a predicate
-- returning a deterministically ordered list.
exprsSomeFreeVarsList ::
  InterestingVarFun -> -- Says which 'Var's are interesting
  [CoreExpr] ->
  [Var]
exprsSomeFreeVarsList fv_cand es =
  fvVarList $ filterFV fv_cand $ mapUnionFV expr_fvs es

-- | Finds free variables in several expressions selected by a predicate
-- returning a deterministic set.

{-
exprsSomeFreeVarsDSet :: InterestingVarFun -- ^ Says which 'Var's are interesting
                      -> [CoreExpr]
                      -> DVarSet
exprsSomeFreeVarsDSet fv_cand e =
  fvDVarSet $ filterFV fv_cand $ mapUnionFV expr_fvs e
-}

--      Comment about obsolete code
-- We used to gather the free variables the RULES at a variable occurrence
-- with the following cryptic comment:
--     "At a variable occurrence, add in any free variables of its rule rhss
--     Curiously, we gather the Id's free *type* variables from its binding
--     site, but its free *rule-rhs* variables from its usage sites.  This
--     is a little weird.  The reason is that the former is more efficient,
--     but the latter is more fine grained, and a makes a difference when
--     a variable mentions itself one of its own rule RHSs"
-- Not only is this "weird", but it's also pretty bad because it can make
-- a function seem more recursive than it is.  Suppose
--      f  = ...g...
--      g  = ...
--         RULE g x = ...f...
-- Then f is not mentioned in its own RHS, and needn't be a loop breaker
-- (though g may be).  But if we collect the rule fvs from g's occurrence,
-- it looks as if f mentions itself.  (This bites in the eftInt/eftIntFB
-- code in GHC.Enum.)
--
-- Anyway, it seems plain wrong.  The RULE is like an extra RHS for the
-- function, so its free variables belong at the definition site.
--
-- Deleted code looked like
--     foldVarSet add_rule_var var_itself_set (idRuleVars var)
--     add_rule_var var set | keep_it fv_cand in_scope var = extendVarSet set var
--                          | otherwise                    = set
--      SLPJ Feb06

addBndr :: CoreBndr -> FV -> FV
addBndr bndr fv fv_cand in_scope acc =
  ( -- varTypeTyCoFVs bndr `unionFV`
    -- Include type variables in the binder's type
    --      (not just Ids; coercion variables too!)
    FV.delFV bndr fv
  )
    fv_cand
    in_scope
    acc

--addBndrs :: [CoreBndr] -> FV -> FV
--addBndrs bndrs fv = foldr addBndr fv bndrs

expr_fvs :: CoreExpr -> FV
expr_fvs (LC.Var var) fv_cand in_scope acc = FV.unitFV var fv_cand in_scope acc
expr_fvs (LC.App fun arg) fv_cand in_scope acc =
  (expr_fvs fun `unionFV` expr_fvs arg) fv_cand in_scope acc
expr_fvs (LC.Lam bndr body) fv_cand in_scope acc =
  addBndr bndr (expr_fvs body) fv_cand in_scope acc

---------
exprs_fvs :: [CoreExpr] -> FV
exprs_fvs exprs = mapUnionFV expr_fvs exprs

{-
************************************************************************
*                                                                      *
\section{Free names}
*                                                                      *
************************************************************************
-}

{-
************************************************************************
*                                                                      *
\section[freevars-everywhere]{Attaching free variables to every sub-expression}
*                                                                      *
************************************************************************
-}

{-
type FVAnn = DVarSet  -- See Note [The FVAnn invariant]

{- Note [The FVAnn invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Invariant: a FVAnn, say S, is closed:
  That is: if v is in S,
           then freevars( v's type/kind ) is also in S
-}

-- | Every node in a binding group annotated with its
-- (non-global) free variables, both Ids and TyVars, and type.
type CoreBindWithFVs = AnnBind Id FVAnn

-- | Every node in an expression annotated with its
-- (non-global) free variables, both Ids and TyVars, and type.
-- NB: see Note [The FVAnn invariant]
type CoreExprWithFVs  = AnnExpr  Id FVAnn
type CoreExprWithFVs' = AnnExpr' Id FVAnn

-- | Every node in an expression annotated with its
-- (non-global) free variables, both Ids and TyVars, and type.
type CoreAltWithFVs = AnnAlt Id FVAnn

freeVarsOf :: CoreExprWithFVs -> DIdSet
-- ^ Inverse function to 'freeVars'
freeVarsOf (fvs, _) = fvs

-- | Extract the vars reported in a FVAnn
freeVarsOfAnn :: FVAnn -> DIdSet
freeVarsOfAnn fvs = fvs

noFVs :: VarSet
noFVs = emptyVarSet

aFreeVar :: Var -> DVarSet
aFreeVar = unitDVarSet

unionFVs :: DVarSet -> DVarSet -> DVarSet
unionFVs = unionDVarSet

unionFVss :: [DVarSet] -> DVarSet
unionFVss = unionDVarSets

delBindersFV :: [Var] -> DVarSet -> DVarSet
delBindersFV bs fvs = foldr delBinderFV fvs bs

delBinderFV :: Var -> DVarSet -> DVarSet
-- This way round, so we can do it multiple times using foldr

-- (b `delBinderFV` s)
--   * removes the binder b from the free variable set s,
--   * AND *adds* to s the free variables of b's type
--
-- This is really important for some lambdas:
--      In (\x::a -> x) the only mention of "a" is in the binder.
--
-- Also in
--      let x::a = b in ...
-- we should really note that "a" is free in this expression.
-- It'll be pinned inside the /\a by the binding for b, but
-- it seems cleaner to make sure that a is in the free-var set
-- when it is mentioned.
--
-- This also shows up in recursive bindings.  Consider:
--      /\a -> letrec x::a = x in E
-- Now, there are no explicit free type variables in the RHS of x,
-- but nevertheless "a" is free in its definition.  So we add in
-- the free tyvars of the types of the binders, and include these in the
-- free vars of the group, attached to the top level of each RHS.
--
-- This actually happened in the defn of errorIO in IOBase.hs:
--      errorIO (ST io) = case (errorIO# io) of
--                          _ -> bottom
--                        where
--                          bottom = bottom -- Never evaluated

delBinderFV b s = (s `delDVarSet` b) `unionFVs` dVarTypeTyCoVars b
        -- Include coercion variables too!
-}

--idFreeVars :: Id -> VarSet
--idFreeVars id = fvVarSet $ idFVs id

--dIdFreeVars :: Id -> DVarSet
--dIdFreeVars id = fvDVarSet $ idFVs id

{-
idFVs :: Id -> FV
-- Type variables, rule variables, and inline variables
idFVs id =
           varTypeTyCoFVs id `unionFV`
           bndrRuleAndUnfoldingFVs id
-}

{-
************************************************************************
*                                                                      *
\subsection{Free variables (and types)}
*                                                                      *
************************************************************************
-}

{-
freeVarsBind :: CoreBind
             -> DVarSet                     -- Free vars of scope of binding
             -> (CoreBindWithFVs, DVarSet)  -- Return free vars of binding + scope
freeVarsBind (NonRec binder rhs) body_fvs
  = ( AnnNonRec binder rhs2
    , freeVarsOf rhs2 `unionFVs` body_fvs2
                      `unionFVs` bndrRuleAndUnfoldingVarsDSet binder )
    where
      rhs2      = freeVars rhs
      body_fvs2 = binder `delBinderFV` body_fvs

freeVarsBind (Rec binds) body_fvs
  = ( AnnRec (binders `zip` rhss2)
    , delBindersFV binders all_fvs )
  where
    (binders, rhss) = unzip binds
    rhss2        = map freeVars rhss
    rhs_body_fvs = foldr (unionFVs . freeVarsOf) body_fvs rhss2
    binders_fvs  = fvDVarSet $ mapUnionFV bndrRuleAndUnfoldingFVs binders
                   -- See Note [The FVAnn invariant]
    all_fvs      = rhs_body_fvs `unionFVs` binders_fvs
            -- The "delBinderFV" happens after adding the idSpecVars,
            -- since the latter may add some of the binders as fvs

freeVars :: CoreExpr -> CoreExprWithFVs
-- ^ Annotate a 'CoreExpr' with its (non-global) free type
--   and value variables at every tree node.
freeVars = go
  where
    go :: CoreExpr -> CoreExprWithFVs
    go (Var v)
      | isLocalVar v = (aFreeVar v `unionFVs` ty_fvs, AnnVar v)
      | otherwise    = (emptyDVarSet,                 AnnVar v)
      where
        ty_fvs = dVarTypeTyCoVars v
                 -- See Note [The FVAnn invariant]

    go (Lit lit) = (emptyDVarSet, AnnLit lit)
    go (Lam b body)
      = ( b_fvs `unionFVs` (b `delBinderFV` body_fvs)
        , AnnLam b body' )
      where
        body'@(body_fvs, _) = go body
        b_ty  = idType b
        b_fvs = tyCoVarsOfTypeDSet b_ty
                -- See Note [The FVAnn invariant]

    go (App fun arg)
      = ( freeVarsOf fun' `unionFVs` freeVarsOf arg'
        , AnnApp fun' arg' )
      where
        fun'   = go fun
        arg'   = go arg

    go (Case scrut bndr ty alts)
      = ( (bndr `delBinderFV` alts_fvs)
           `unionFVs` freeVarsOf scrut2
           `unionFVs` tyCoVarsOfTypeDSet ty
          -- Don't need to look at (idType bndr)
          -- because that's redundant with scrut
        , AnnCase scrut2 bndr ty alts2 )
      where
        scrut2 = go scrut

        (alts_fvs_s, alts2) = mapAndUnzip fv_alt alts
        alts_fvs            = unionFVss alts_fvs_s

        fv_alt (con,args,rhs) = (delBindersFV args (freeVarsOf rhs2),
                                 (con, args, rhs2))
                              where
                                 rhs2 = go rhs

    go (Let bind body)
      = (bind_fvs, AnnLet bind2 body2)
      where
        (bind2, bind_fvs) = freeVarsBind bind (freeVarsOf body2)
        body2             = go body

    go (Cast expr co)
      = ( freeVarsOf expr2 `unionFVs` cfvs
        , AnnCast expr2 (cfvs, co) )
      where
        expr2 = go expr
        cfvs  = tyCoVarsOfCoDSet co

    go (Tick tickish expr)
      = ( tickishFVs tickish `unionFVs` freeVarsOf expr2
        , AnnTick tickish expr2 )
      where
        expr2 = go expr
        tickishFVs (Breakpoint _ ids) = mkDVarSet ids
        tickishFVs _                  = emptyDVarSet

    go (Type ty)     = (tyCoVarsOfTypeDSet ty, AnnType ty)
    go (Coercion co) = (tyCoVarsOfCoDSet co, AnnCoercion co)
-}