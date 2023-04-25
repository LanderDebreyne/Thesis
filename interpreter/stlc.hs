import qualified Data.Map as Map
import qualified Data.Set as Set

type Context = Map.Map Name ValueType

type Name = String

typeCheckC :: Comp -> ComputationType -> Context -> Bool
typeCheckC (Return v) (vt, _) ctx = typeCheckV v vt ctx -- SD-Ret
typeCheckC (App (Lam n vt1 c) v2) (vt2, e) ctx = typeCheckC c (Tfunction vt1 (vt2, e), e) (Map.insert n vt1 ctx) && typeCheckV v2 vt1 ctx -- SD-App

typeCheckV :: Value -> ValueType -> Context -> Bool
typeCheckV (Var n i) vt ctx = case Map.lookup n ctx of
  Just vt' -> vt == vt'
  Nothing -> False
typeCheckV (Lam n vt1 c) (Tfunction vt2 (vt3, e)) ctx = typeCheckC c (vt3, e) (Map.insert n vt1 ctx) -- SD-Abs
typeCheckV (Vbool _) Tbool ctx = True -- SD-Bool
typeCheckV (Vint _) Tint c = True -- SD-Int
typeCheckV (Vchar _) Tchar c = True -- SD-Char
typeCheckV (Vstr _) Tstr c = True -- SD-Str
typeCheckV (Vret v) (Tret t) ctx = typeCheckV v t ctx -- SD-Ret
typeCheckV (Vflag v) (Tflag t) ctx = typeCheckV v t ctx -- SD-Flag


-- | Value syntax
data Value 
  = Var Name Int
  | Lam Name ValueType Comp
  -- | Vunit
  -- | Vpair (Value, Value)
  -- | Vhandler Handler
  -- | Vlist [Value]
  -- | Vrec Name Value Value
  -- extensions:
  -- | Vsum (Either Value Value)
  | Vbool Bool
  | Vint Int
  | Vchar Char
  | Vstr String   -- ^ for simplicity, we separate lists and strings
  | Vret Value 
  | Vflag Value
  -- | Vmem (Memory Value)
  -- | Vkey (StdGen)
  deriving (Eq)


-- | Computation syntax
data Comp
  = Return Value                                    -- ^ return v
  -- | Op Name Value (Dot Name Comp)                  -- ^ op l v (y.c)
  -- | Sc Name Value (Dot Name Comp) (Dot Name Comp)  -- ^ sc l v (y.c1) (z.c2)
  -- | For Name Value (Dot Name Comp) (Dot Name Comp) -- ^ for l v (y.c1) (z.c2)
  -- | Handle Handler Comp                             -- ^ v ★ c
  -- | Do Name Comp Comp                               -- ^ do x <- c1 in c2
  -- | Rec Name Comp Comp                              -- ^ rec x c1 c2
  | App Value Value                                 -- ^ v1 v2
  -- | Let Name Value Comp                             -- ^ let x = v in c
  -- | Letrec Name Value Comp                          -- ^ letrec x = c in c
  -- extensions:
  -- We implement most functions in the paper as built-in functions
  -- because the interpreter doesn't support pattern matching and recursive functions.
  | If Value Comp Comp
  -- | Case Value Name Comp Name Comp
  -- | Unop Op1 Value
  -- | Binop Op2 Value Value
  | Undefined                                     -- ^ undefined
  deriving (Eq)

-- | Label syntax
data Label = Lop Name ValueType ValueType 
             | Lsc Name ValueType ValueType
             | Lfor Name ValueType 
             deriving (Eq, Show)


  -- | Value type syntax
data ValueType = Tunit
            | Tpair ValueType ValueType
            | Tfunction ValueType ComputationType
            | THandler ComputationType ComputationType
            | Tlist ValueType
            | TValVar Name Int
            | TOpAbs Name Int ValueType
            | Tapp ValueType ValueType
            | Tsum ValueType ValueType
            | Tint 
            | Tbool
            | Tstr
            | Tchar
            | Tflag ValueType 
            | Tret ValueType
            | Tmem
            | Tkey
            deriving (Eq, Show)

-- | Effect type syntax
type EffectType = Set.Set Label

-- | Computation type syntax
type ComputationType = (ValueType, EffectType)