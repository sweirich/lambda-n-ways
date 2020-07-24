{-# OPTIONS  -Wall               #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Kit where

import Control.Monad.State

-- Types and the corresponding singleton
data Ty = TyUnit | TyBool | TyFunc Ty Ty
data STy :: Ty -> * where
  STyUnit :: STy 'TyUnit
  STyBool :: STy 'TyBool
  STyFunc :: STy a -> STy b -> STy ('TyFunc a b)

-- A context is a list of types
data Con = Null | Cons Con Ty
data SCon :: Con -> * where
  SNull :: SCon 'Null
  SCons :: SCon g -> STy a -> SCon ('Cons g a)

-- A variable is a fancy de Bruijn index
data Var :: Con -> Ty -> * where
  Z :: Var ('Cons g a) a
  S :: Var g a -> Var ('Cons g b) a

data Term :: Con -> Ty -> * where
  TeVar   :: Var g a -> Term g a
  TeLam   :: Term ('Cons g a) b -> Term g ('TyFunc a b)
  TeApp   :: STy a -> Term g ('TyFunc a b) -> Term g a -> Term g b
  TeUnit  :: Term g 'TyUnit
  TeTrue  :: Term g 'TyBool
  TeFalse :: Term g 'TyBool
  TeIfte  :: Term g 'TyBool -> Term g a -> Term g a -> Term g a

-- An (evaluation) environment is a collection of environment
-- values covering a given context `g`.

type Environment (d :: Con) (e :: Con -> Ty -> *) (g :: Con) =
  forall a. STy a -> Var g a -> e d a

envNull :: Environment d e 'Null
envNull v = case v of {}

envCons :: Environment d e g -> e d a -> Environment d e ('Cons g a)
envCons _   e _ Z     = e
envCons env _ a (S v) = env a v

type Included g d = Environment d Var g

refl :: forall g. Included g g
refl _ = id

top :: forall d g a. Included g d -> Included g ('Cons d a)
top inc a = S . inc a

pop :: forall d g a. Included g d -> Included ('Cons g a) ('Cons d a)
pop _   _ Z     = Z
pop inc a (S v) = S $ inc a v

trans :: Included g h -> Included h i -> Included g i
trans inc1 inc2 a = inc2 a . inc1 a

data Semantics (e :: Con -> Ty -> *) (m :: Con -> Ty -> *) =
  Semantics { weak  :: forall g d a. STy a -> Included g d -> e g a -> e d a
            , embed :: forall g a. STy a -> Var g a -> e g a
            , var   :: forall g a. STy a -> e g a -> m g a
            , app   :: forall g a b. STy a -> m g ('TyFunc a b) -> m g a -> m g b
            , lam   :: forall g a b. (forall d. Included g d -> e d a -> m d b) -> m g ('TyFunc a b)
            , unit  :: forall g. m g 'TyUnit
            , true  :: forall g. m g 'TyBool
            , false :: forall g. m g 'TyBool
            , ifte  :: forall g a. STy a -> m g 'TyBool -> m g a -> m g a -> m g a
            }


wkEnv :: forall h d g e m. Semantics e m -> Included d h -> Environment d e g -> Environment h e g
wkEnv Semantics{..} inc env a v = weak a inc $ env a v

semanticsTerm :: forall e m d g a. Semantics e m -> STy a -> Term g a -> Environment d e g -> m d a
semanticsTerm sem@Semantics{..} = go where
  go :: forall d' g' a'. STy a' -> Term g' a' -> Environment d' e g' -> m d' a'
  go a             (TeVar v)      env = var a $ env a v
  go (STyFunc _ b) (TeLam t)      env = lam $ \ inc v -> go b t (envCons (wkEnv sem inc env) v)
  go b             (TeApp a f t)  env = app a (go (STyFunc a b) f env) (go a t env)
  go _             TeUnit         _   = unit
  go _             TeTrue         _   = true
  go _             TeFalse        _   = false
  go a             (TeIfte b l r) env = ifte a (go STyBool b env) (go a l env) (go a r env)

evalTerm :: forall e m g a. Semantics e m -> SCon g -> STy a -> Term g a -> m g a
evalTerm sem@Semantics{..} g a t = semanticsTerm sem a t (env g) where
  env :: forall g'. SCon g' -> Environment g' e g'
  env SNull         = envNull
  env (SCons sg sa) = envCons (wkEnv sem (top refl) $ env sg) (embed sa Z)

------------------------------------------------------------------------
-- Syntactic Semantics
------------------------------------------------------------------------

renaming :: Semantics Var Term
renaming =
  Semantics { weak  = \ a inc v -> inc a v
            , embed = const id
            , var   = const TeVar
            , app   = TeApp
            , lam   = \ t -> TeLam $ t (top refl) Z
            , unit  = TeUnit
            , true  = TeTrue
            , false = TeFalse
            , ifte  = const TeIfte
            }

weakTe :: STy a -> Included g d -> Term g a -> Term d a
weakTe a inc t = semanticsTerm renaming a t inc

substitution :: Semantics Term Term
substitution =
  Semantics { weak  = weakTe
            , embed = const TeVar
            , var   = const id
            , app   = TeApp
            , lam   = \ t -> TeLam $ t (top refl) (TeVar Z)
            , unit  = TeUnit
            , true  = TeTrue
            , false = TeFalse
            , ifte  = const TeIfte
            }

------------------------------------------------------------------------
-- Pretty Printing Semantics
------------------------------------------------------------------------

newtype Constant2 k (g :: Con) (s :: Ty) = Constant2 { runConstant2 :: k }

prettyPrinting :: Semantics (Constant2 String) (Constant2 (State [String] String))
prettyPrinting =
  Semantics { weak  = \ _ _ -> Constant2 . runConstant2
            , embed = const $ Constant2 . show . deBruijn
            , var   = const $ Constant2 . return . runConstant2
            , app   = \ _ mf mt ->
                      Constant2 $ do
                        f <- runConstant2 mf
                        t <- runConstant2 mt
                        return $ f ++ " (" ++ t ++ ")"
            , lam   = \ mbody -> Constant2 $ do
                        ys       <- get
                        let (x:xs) = ys
                        ()       <- put xs
                        body     <- runConstant2 $ mbody (top refl) (Constant2 x)
                        return $ '\\' : x ++ ". " ++ body
            , unit  = Constant2 $ return "()"
            , true  = Constant2 $ return "True"
            , false = Constant2 $ return "False"
            , ifte  = \ _ mb ml mr ->
                      Constant2 $ do
                        b <- runConstant2 mb
                        l <- runConstant2 ml
                        r <- runConstant2 mr
                        return $ "if (" ++ b ++ ") then (" ++ l ++ ") else (" ++ r ++ ")"
            }
  where
    deBruijn :: forall g a. Var g a -> Integer
    deBruijn Z     = 0
    deBruijn (S v) = 1 + deBruijn v

prettyPrint :: forall g a. SCon g -> STy a -> Term g a -> String
prettyPrint g a t = evalState (runConstant2 $ evalTerm prettyPrinting g a t) names
  where names = fmap (:[]) alpha ++ alphaInt
        alpha    = ['a'..'z']
        alphaInt = concat $ fmap (\ i -> fmap (: show i) alpha) [(0 :: Integer)..]


------------------------------------------------------------------------
-- Normalization by Evaluation
------------------------------------------------------------------------

-- We now build a Kripke model for these terms by induction
-- on the type.

type family Value (g :: Con) (t :: Ty) where
  Value g 'TyUnit       = ()
  Value g 'TyBool       = Term g 'TyBool
  -- And now... because polymorphic types are not allowed here
  -- we use `Kripke`. However newtypes are erased during compilation
  -- so the model definiton is indeed tagless in the end.
  Value g ('TyFunc a b) = Kripke g a b

newtype Kripke g a b = Kripke { runKripke :: forall h. Included g h -> Value h a -> Value h b }

weakValue :: forall d g a. STy a -> Included g d -> Value g a -> Value d a
weakValue STyUnit       _   v = v
weakValue STyBool       inc v = weakTe STyBool inc v
weakValue (STyFunc _ _) inc v = Kripke $ \ inc' -> runKripke v (trans inc inc')

reflect :: forall g a. STy a -> Term g a -> Value g a
reflect STyUnit       _ = ()
reflect STyBool       t = t
reflect (STyFunc a b) t = Kripke $ \ inc v -> reflect b $ TeApp a (weakTe (STyFunc a b) inc t) $ reify a v

reify :: forall g a. STy a -> Value g a -> Term g a
reify STyUnit         _ = TeUnit
reify STyBool         v = v
reify (STyFunc sa sb) v = TeLam $ reify sb $ body sa v where

  var0 :: forall c. STy c -> Value ('Cons g c) c
  var0 sc = reflect sc (TeVar Z :: Term ('Cons g c) c)

  body :: forall c d. STy c -> Kripke g c d -> Value ('Cons g c) d
  body sc f = runKripke f (top refl :: Included g ('Cons g c)) $ var0 sc

-- Value, being a type family, cannot be partially applied.
-- We introduce PValue, a newtype which can be *P*artially applied.
newtype PValue (g :: Con) (a :: Ty) = PValue { runPValue :: Value g a }

weakPValue :: forall d g a. STy a -> Included g d -> PValue g a -> PValue d a
weakPValue a inc = PValue . weakValue a inc . runPValue

normalisation :: Semantics PValue PValue
normalisation =
  Semantics { weak  = weakPValue
            , embed = \ sa v -> PValue $ reflect sa $ TeVar v
            , var   = \ _ -> id
            , app   = \ _ f t -> PValue $ runKripke (runPValue f) refl $ runPValue t
            , lam   = \ t -> PValue $ Kripke $ \ inc -> runPValue . t inc . PValue
            , unit  = PValue ()
            , true  = PValue TeTrue
            , false = PValue TeFalse
            , ifte  = \ a b l r -> PValue $ ifte a (runPValue b) (runPValue l) (runPValue r)
            } where
  ifte :: STy a -> Value g 'TyBool -> Value g a -> Value g a -> Value g a
  ifte _ TeTrue  l _ = l
  ifte _ TeFalse _ r = r
  ifte a b       l r = reflect a $ TeIfte (reify STyBool b) (reify a l) (reify a r)

normalise :: SCon g -> STy a -> Term g a -> Term g a
normalise sg sa t = reify sa $ runPValue $ evalTerm normalisation sg sa t

------------------------------------------------------------------------
-- Benchmark normalization function ?
------------------------------------------------------------------------

nf :: Semantics Term Term
nf =
  Semantics { weak = 
