module NBE.Aelig where

-- de Bruijn index representation
-- of syntax
data DB
  = Var Int
  | Lam DB
  | App DB DB
  | Unit
  | Bool Bool
  | If DB DB DB
  | Print DB
  deriving (Eq, Show)

-- syntacic values
isVal :: DB -> Bool
isVal (Lam _) = True
isVal Unit = True
isVal (Bool _) = True
isVal _ = False

-- semantic values
data Val
  = ABS {app :: Val -> (String, Val)}
  | UNIT
  | BOOL Bool

instance Show Val where
  show (ABS _f) = show "<fn>" -- cannot display function values
  show UNIT = show "()"
  show (BOOL b) = show b

type Env = [Val]

interpret :: DB -> Env -> (String, Val)
interpret (Var n) rho = (mempty, rho !! n)
interpret (Lam r) rho = (mempty, ABS (\a -> interpret r (a : rho)))
interpret (App r s) rho = (m1 <> m2 <> m3, v)
  where
    (m1, vr) = interpret r rho
    (m2, vs) = interpret s rho
    (m3, v) = vr `app` vs
interpret Unit _r = (mempty, UNIT)
interpret (Bool b) _r = (mempty, BOOL b)
interpret (If b a1 a2) r = (m1 <> m2, v)
  where
    (m1, vr) = (interpret b r)
    (m2, v) = if_ vr (interpret a1 r) (interpret a2 r)
interpret (Print s) r = (m <> show v, UNIT)
  where
    (m, v) = interpret s r

-- semantic if
if_ :: Val -> p -> p -> p
if_ (BOOL b) a1 a2 = if b then a1 else a2
if_ _ _ _ = error "WRONG"
