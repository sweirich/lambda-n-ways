{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

module Core.Subst
  ( -- * Main data types
    Subst (..), -- Implementation exported for supercompiler's Renaming.hs only
    IdSubstEnv,
    InScopeSet,

    -- ** Substituting into expressions and related types

    --deShadowBinds, substSpec, substRulesForImportedIds,
    --substTy, substCo,
    substExpr,
    substExprSC,
    --substBind, substBindSC,
    --substUnfolding, substUnfoldingSC,
    lookupIdSubst,
    --lookupTCvSubst,
    substIdType,
    substIdOcc,
    --substTickish, substDVarSet, substIdInfo,

    -- ** Operations on substitutions
    emptySubst,
    mkEmptySubst,
    mkSubst,
    mkOpenSubst,
    substInScope,
    isEmptySubst,
    extendIdSubst,
    extendIdSubstList, --extendTCvSubst, extendTvSubstList,
    extendSubst,
    extendSubstList,
    extendSubstWithVar,
    zapSubstEnv,
    addInScopeSet,
    extendInScope,
    extendInScopeList,
    extendInScopeIds,
    isInScope,
    setInScope, --getTCvSubst, extendTvSubst, extendCvSubst,
    delBndr,
    delBndrs,

    -- ** Substituting and cloning binders
    substBndr,
    substBndrs,
    substRecBndrs, --substTyVarBndr, substCoVarBndr,
    --cloneBndr, cloneBndrs, cloneIdBndr, cloneIdBndrs, cloneRecIdBndrs,
  )
where

import Core.Core
import Core.CoreFVs
import Core.Unique
import Core.VarEnv
import Core.VarSet
import Data.List (mapAccumL)
import qualified Util.Syntax.Lambda as LC

{-

import GHC.Core
import GHC.Core.FVs
import GHC.Core.Seq
import GHC.Core.Utils
import qualified GHC.Core.Type as Type
import qualified GHC.Core.Coercion as Coercion

        -- We are defining local versions
import GHC.Core.Type hiding
   ( substTy, extendTvSubst, extendCvSubst, extendTvSubstList
   , isInScope, substTyVarBndr, cloneTyVarBndr )
import GHC.Core.Coercion hiding ( substCo, substCoVarBndr )

import GHC.Builtin.Names
import GHC.Types.Var.Set
import GHC.Types.Var.Env
import GHC.Types.Id
import GHC.Types.Name     ( Name )
import GHC.Types.Var
import GHC.Types.Id.Info
import GHC.Types.Unique.Supply
import GHC.Data.Maybe
import GHC.Utils.Misc
import GHC.Utils.Outputable
import Data.List

-}

data Subst
  = Subst
      InScopeSet -- Variables in in scope (both Ids and TyVars) /after/
      -- applying the substitution
      IdSubstEnv -- Substitution from NcIds to CoreExprs

-- | An environment for substituting for 'Id's
type IdSubstEnv = IdEnv CoreExpr -- Domain is NcIds, i.e. not coercions

----------------------------
isEmptySubst :: Subst -> Bool
isEmptySubst (Subst _ id_env) =
  isEmptyVarEnv id_env

emptySubst :: Subst
emptySubst = Subst emptyInScopeSet emptyVarEnv

mkEmptySubst :: InScopeSet -> Subst
mkEmptySubst in_scope = Subst in_scope emptyVarEnv

mkSubst :: InScopeSet -> IdSubstEnv -> Subst
mkSubst in_scope ids = Subst in_scope ids

-- | Find the in-scope set: see TyCoSubst Note [The substitution invariant]
substInScope :: Subst -> InScopeSet
substInScope (Subst in_scope _) = in_scope

-- | Remove all substitutions for 'Id's and 'Var's that might have been built up
-- while preserving the in-scope set
zapSubstEnv :: Subst -> Subst
zapSubstEnv (Subst in_scope _) = Subst in_scope emptyVarEnv

-- | Add a substitution for an 'Id' to the 'Subst': you must ensure that the in-scope set is
-- such that TyCoSubst Note [The substitution invariant]
-- holds after extending the substitution like this
extendIdSubst :: Subst -> Id -> CoreExpr -> Subst
-- ToDo: add an ASSERT that fvs(subst-result) is already in the in-scope set
extendIdSubst (Subst in_scope ids) v r =
  Subst in_scope (extendVarEnv ids v r)

-- | Adds multiple 'Id' substitutions to the 'Subst': see also 'extendIdSubst'
extendIdSubstList :: Subst -> [(Id, CoreExpr)] -> Subst
extendIdSubstList (Subst in_scope ids) prs =
  Subst in_scope (extendVarEnvList ids prs)

-- | Add a substitution appropriate to the thing being substituted
--   (whether an expression, type, or coercion). See also
--   'extendIdSubst', 'extendTvSubst', 'extendCvSubst'
extendSubst :: Subst -> Var -> CoreArg -> Subst
extendSubst subst var arg =
  extendIdSubst subst var arg

extendSubstWithVar :: Subst -> Var -> Var -> Subst
extendSubstWithVar subst v1 v2 =
  extendIdSubst subst v1 (LC.Var v2)

-- | Add a substitution as appropriate to each of the terms being
--   substituted (whether expressions, types, or coercions). See also
--   'extendSubst'.
extendSubstList :: Subst -> [(Var, CoreArg)] -> Subst
extendSubstList subst [] = subst
extendSubstList subst ((var, rhs) : prs) = extendSubstList (extendSubst subst var rhs) prs

-- | Find the substitution for an 'Id' in the 'Subst'
lookupIdSubst :: String -> Subst -> Id -> CoreExpr
lookupIdSubst doc (Subst in_scope ids) v
  | not (isLocalId v) = LC.Var v
  | Just e <- lookupVarEnv ids v = e
  | Just v' <- lookupInScope in_scope v = LC.Var v'
  -- Vital! See Note [Extending the Subst]
  | otherwise = LC.Var v
{-# INLINEABLE lookupIdSubst #-}

delBndr :: Subst -> Var -> Subst
delBndr (Subst in_scope ids) v =
  Subst in_scope (delVarEnv ids v)

delBndrs :: Subst -> [Var] -> Subst
delBndrs (Subst in_scope ids) vs =
  Subst in_scope (delVarEnvList ids vs)

-- Easiest thing is just delete all from all!

-- | Simultaneously substitute for a bunch of variables
--   No left-right shadowing
--   ie the substitution for   (\x \y. e) a1 a2
--      so neither x nor y scope over a1 a2
mkOpenSubst :: InScopeSet -> [(Var, CoreArg)] -> Subst
mkOpenSubst in_scope pairs =
  Subst
    in_scope
    (mkVarEnv [(id, e) | (id, e) <- pairs, isId id])

------------------------------
isInScope :: Var -> Subst -> Bool
isInScope v (Subst in_scope _) = v `elemInScopeSet` in_scope

-- | Add the 'Var' to the in-scope set, but do not remove
-- any existing substitutions for it
addInScopeSet :: Subst -> VarSet -> Subst
addInScopeSet (Subst in_scope ids) vs =
  Subst (in_scope `extendInScopeSetSet` vs) ids

-- | Add the 'Var' to the in-scope set: as a side effect,
-- and remove any existing substitutions for it
extendInScope :: Subst -> Var -> Subst
extendInScope (Subst in_scope ids) v =
  Subst
    (in_scope `extendInScopeSet` v)
    (ids `delVarEnv` v)

-- | Add the 'Var's to the in-scope set: see also 'extendInScope'
extendInScopeList :: Subst -> [Var] -> Subst
extendInScopeList (Subst in_scope ids) vs =
  Subst
    (in_scope `extendInScopeSetList` vs)
    (ids `delVarEnvList` vs)

-- | Optimized version of 'extendInScopeList' that can be used if you are certain
-- all the things being added are 'Id's and hence none are 'TyVar's or 'CoVar's
extendInScopeIds :: Subst -> [Id] -> Subst
extendInScopeIds (Subst in_scope ids) vs =
  Subst
    (in_scope `extendInScopeSetList` vs)
    (ids `delVarEnvList` vs)

setInScope :: Subst -> InScopeSet -> Subst
setInScope (Subst _ ids) in_scope = Subst in_scope ids

{-
************************************************************************
*                                                                      *
        Substituting expressions
*                                                                      *
************************************************************************
-}

-- | Apply a substitution to an entire 'CoreExpr'. Remember, you may only
-- apply the substitution /once/:
-- See Note [Substitutions apply only once] in GHC.Core.TyCo.Subst
--
-- Do *not* attempt to short-cut in the case of an empty substitution!
-- See Note [Extending the Subst]
substExprSC :: String -> Subst -> CoreExpr -> CoreExpr
substExprSC doc subst orig_expr
  | isEmptySubst subst = orig_expr
  | otherwise -- pprTrace "enter subst-expr" (doc $$ ppr orig_expr) $
    =
    subst_expr doc subst orig_expr

substExpr :: String -> Subst -> CoreExpr -> CoreExpr
substExpr doc subst orig_expr = subst_expr doc subst orig_expr

subst_expr :: String -> Subst -> CoreExpr -> CoreExpr
subst_expr doc subst expr =
  go expr
  where
    go (LC.Var v) = lookupIdSubst ("subst_expr") subst v
    go (LC.App fun arg) = LC.App (go fun) (go arg)
    go (LC.Lam bndr body) = LC.Lam bndr' (subst_expr doc subst' body)
      where
        (subst', bndr') = substBndr subst bndr

-- | De-shadowing the program is sometimes a useful pre-pass. It can be done simply
-- by running over the bindings with an empty substitution, because substitution
-- returns a result that has no-shadowing guaranteed.
--
-- (Actually, within a single /type/ there might still be shadowing, because
-- 'substTy' is a no-op for the empty substitution, but that's probably OK.)
--
-- [Aug 09] This function is not used in GHC at the moment, but seems so
--          short and simple that I'm going to leave it here
-- deShadowBinds :: CoreProgram -> CoreProgram
-- deShadowBinds binds = snd (mapAccumL substBind emptySubst binds)

{-
************************************************************************
*                                                                      *
        Substituting binders
*                                                                      *
************************************************************************

Remember that substBndr and friends are used when doing expression
substitution only.  Their only business is substitution, so they
preserve all IdInfo (suitably substituted).  For example, we *want* to
preserve occ info in rules.
-}

-- | Substitutes a 'Var' for another one according to the 'Subst' given, returning
-- the result and an updated 'Subst' that should be used by subsequent substitutions.
-- 'IdInfo' is preserved by this process, although it is substituted into appropriately.
substBndr :: Subst -> Var -> (Subst, Var)
substBndr subst bndr =
  substIdBndr ("var-bndr") subst subst bndr

-- | Applies 'substBndr' to a number of 'Var's, accumulating a new 'Subst' left-to-right
substBndrs :: Subst -> [Var] -> (Subst, [Var])
substBndrs subst bndrs = mapAccumL substBndr subst bndrs

-- | Substitute in a mutually recursive group of 'Id's
substRecBndrs :: Subst -> [Id] -> (Subst, [Id])
substRecBndrs subst bndrs =
  (new_subst, new_bndrs)
  where
    -- Here's the reason we need to pass rec_subst to subst_id
    (new_subst, new_bndrs) = mapAccumL (substIdBndr ("rec-bndr") new_subst) subst bndrs

substIdBndr ::
  String ->
  -- | Substitution to use for the IdInfo
  Subst ->
  Subst ->
  -- | Substitution and Id to transform
  Id ->
  -- | Transformed pair
  -- NB: unfolding may be zapped
  (Subst, Id)
substIdBndr _doc rec_subst subst@(Subst in_scope env) old_id =
  -- pprTrace "substIdBndr" (doc $$ ppr old_id $$ ppr in_scope) $
  (Subst (in_scope `extendInScopeSet` new_id) new_env, new_id)
  where
    id1 = uniqAway in_scope old_id -- id1 is cloned if necessary
    id2 = id1

    -- new_id has the right IdInfo
    -- The lazy-set is because we're in a loop here, with
    -- rec_subst, when dealing with a mutually-recursive group
    new_id = id2
    --mb_new_info = substIdInfo rec_subst id2 (idInfo id2)
    -- NB: unfolding info may be zapped

    -- Extend the substitution if the unique has changed
    -- See the notes with substTyVarBndr for the delVarEnv
    new_env
      | no_change = delVarEnv env old_id
      | otherwise = extendVarEnv env old_id (LC.Var new_id)

    no_change = id1 == old_id

-- See Note [Extending the Subst]
-- it's /not/ necessary to check mb_new_info and no_type_change

{-
Now a variant that unconditionally allocates a new unique.
It also unconditionally zaps the OccInfo.
-}

{-
-- | Very similar to 'substBndr', but it always allocates a new 'Unique' for
-- each variable in its output.  It substitutes the IdInfo though.
cloneIdBndr :: Subst -> UniqSupply -> Id -> (Subst, Id)
cloneIdBndr subst us old_id
  = clone_id subst subst (old_id, uniqFromSupply us)

-- | Applies 'cloneIdBndr' to a number of 'Id's, accumulating a final
-- substitution from left to right
cloneIdBndrs :: Subst -> UniqSupply -> [Id] -> (Subst, [Id])
cloneIdBndrs subst us ids
  = mapAccumL (clone_id subst) subst (ids `zip` uniqsFromSupply us)

cloneBndrs :: Subst -> UniqSupply -> [Var] -> (Subst, [Var])
-- Works for all kinds of variables (typically case binders)
-- not just Ids
cloneBndrs subst us vs
  = mapAccumL (\subst (v, u) -> cloneBndr subst u v) subst (vs `zip` uniqsFromSupply us)

cloneBndr :: Subst -> Unique -> Var -> (Subst, Var)
cloneBndr subst uniq v
  | isTyVar v = cloneTyVarBndr subst v uniq
  | otherwise = clone_id subst subst (v,uniq)  -- Works for coercion variables too

-- | Clone a mutually recursive group of 'Id's
cloneRecIdBndrs :: Subst -> UniqSupply -> [Id] -> (Subst, [Id])
cloneRecIdBndrs subst us ids
  = (subst', ids')
  where
    (subst', ids') = mapAccumL (clone_id subst') subst
                               (ids `zip` uniqsFromSupply us)

-- Just like substIdBndr, except that it always makes a new unique
-- It is given the unique to use
clone_id    :: Subst                    -- Substitution for the IdInfo
            -> Subst -> (Id, Unique)    -- Substitution and Id to transform
            -> (Subst, Id)              -- Transformed pair

clone_id rec_subst subst@(Subst in_scope idvs ) (old_id, uniq)
  = (Subst (in_scope `extendInScopeSet` new_id) new_idvs tvs new_cvs, new_id)
  where
    id1     = setVarUnique old_id uniq
    id2     = substIdType subst id1
    new_id  = maybeModifyIdInfo (substIdInfo rec_subst id2 (idInfo old_id)) id2
    (new_idvs, new_cvs) | isCoVar old_id = (idvs, extendVarEnv cvs old_id (mkCoVarCo new_id))
                        | otherwise      = (extendVarEnv idvs old_id (Var new_id), cvs)
-}

{-
************************************************************************
*                                                                      *
\section{IdInfo substitution}
*                                                                      *
************************************************************************
-}

substIdType :: Subst -> Id -> Id
substIdType subst@(Subst _ _) id = id

------------------
substIdOcc :: Subst -> Id -> Id
-- These Ids should not be substituted to non-Ids
substIdOcc subst v = case lookupIdSubst ("substIdOcc") subst v of
  LC.Var v' -> v'
  other -> error $ "substIdOcc"

------------------
{-}
substDVarSet :: Subst -> DVarSet -> DVarSet
substDVarSet subst fvs
  = mkDVarSet $ fst $ foldr (subst_fv subst) ([], emptyVarSet) $ dVarSetElems fvs
  where
  subst_fv subst fv acc
     | isId fv = expr_fvs (lookupIdSubst (text "substDVarSet") subst fv) isLocalVar emptyVarSet $! acc
     | otherwise = tyCoFVsOfType (lookupTCvSubst subst fv) (const True) emptyVarSet $! acc
-}

{- Note [Substitute lazily]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
The functions that substitute over IdInfo must be pretty lazy, because
they are knot-tied by substRecBndrs.

One case in point was #10627 in which a rule for a function 'f'
referred to 'f' (at a different type) on the RHS.  But instead of just
substituting in the rhs of the rule, we were calling simpleOptExpr, which
looked at the idInfo for 'f'; result <<loop>>.

In any case we don't need to optimise the RHS of rules, or unfoldings,
because the simplifier will do that.

Note [substTickish]
~~~~~~~~~~~~~~~~~~~~~~
A Breakpoint contains a list of Ids.  What happens if we ever want to
substitute an expression for one of these Ids?

First, we ensure that we only ever substitute trivial expressions for
these Ids, by marking them as NoOccInfo in the occurrence analyser.
Then, when substituting for the Id, we unwrap any type applications
and abstractions to get back to an Id, with getIdFromTrivialExpr.

Second, we have to ensure that we never try to substitute a literal
for an Id in a breakpoint.  We ensure this by never storing an Id with
an unlifted type in a Breakpoint - see GHC.HsToCore.Coverage.mkTickish.
Breakpoints can't handle free variables with unlifted types anyway.
-}

{-
Note [Worker inlining]
~~~~~~~~~~~~~~~~~~~~~~
A worker can get substituted away entirely.
        - it might be trivial
        - it might simply be very small
We do not treat an InlWrapper as an 'occurrence' in the occurrence
analyser, so it's possible that the worker is not even in scope any more.

In all all these cases we simply drop the special case, returning to
InlVanilla.  The WARN is just so I can see if it happens a lot.
-}
