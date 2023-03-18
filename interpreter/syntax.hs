module Syntax where

type Name = String

-- | Value syntax
data Value 
  = Var Name Int
  | Lam Name Comp
  | Vunit
  | Vpair (Value, Value)
  | Vhandler Handler
  | Vlist [Value]
  | Vrec Name Value Value
  -- extensions:
  | Vsum (Either Value Value)
  | Vbool Bool
  | Vint Int
  | Vchar Char
  | Vstr String   -- ^ for simplicity, we separate lists and strings
  | Vret Value 
  | Vflag Value
  | Vmem (Memory Value)
  deriving (Eq)

instance Show Value where
  show (Var x i) = x
  show (Lam x c) = ("\\ " ++ x ++ ". " ++ show c)
  show Vunit = "()"
  show (Vpair (v1, v2)) = "(" ++ show v1 ++ ", " ++ show v2 ++ ")"
  show (Vhandler h) = show h
  show (Vlist vs) = show vs 
  show (Vrec x v1 v2) = "rec " ++ x ++ " = " ++ show v1 ++ " in " ++ show v2
  show (Vsum (Left v)) = "Left " ++ show v
  show (Vsum (Right v)) = "Right " ++ show v
  show (Vbool b) = show b
  show (Vint i) = show i
  show (Vchar c) = show c
  show (Vstr s) = show s
  show (Vret v) = "Vreturn " ++ show v
  show (Vflag v) = "flag " ++ show v
  show (Vmem m) = show m




-- | Handler syntax
data Handler = Handler
  { hname   :: Name                                   -- ^ handler name
  , oplist  :: [Name]                                 -- ^ algebraic operations names
  , sclist  :: [Name]                                 -- ^ scoped operations names
  , hreturn :: (Name, Comp)                           -- ^ (x, c)
  , hop     :: Name -> Maybe (Name, Name, Comp)       -- ^ l -> (x, k, c)
  , hsc     :: Name -> Maybe (Name, Name, Name, Comp) -- ^ l -> (x, p, k, c)
  , hfwd    :: (Name, Name, Name, Comp)               -- ^ (f, p, k, c)
  , hfor    :: Maybe (Name, Name, Name, Comp)         -- ^ (x, l, k, c)
  } | 
  Parallel {
    pfor :: (Name, Name, Name, Comp)                  -- ^ (x, l, k, c)
    , hreturn :: (Name, Comp)                         -- ^ (x, c) 
  }
instance Show Handler where
  show (Handler name _ _ _ _ _ _ _) = "handler{" ++ name ++ "}"
  show (Parallel _ _ ) = "parallel{}"

instance Eq Handler where
  Handler x _ _ _ _ _ _ _ == Handler y _ _ _ _ _ _ _ = x == y
  Parallel _ _ == Parallel _ _ = True

infixr 0 :.
data (Dot a b) = a :. b deriving (Eq)

instance Show (Dot Name Comp) where
  show (x :. y) = (show x) ++ ". " ++ (show y) 

-- | Computation syntax
data Comp
  = Return Value                                   -- ^ return v
  | Op Name Value (Dot Name Comp)                  -- ^ op l v (y.c)
  | Sc Name Value (Dot Name Comp) (Dot Name Comp)  -- ^ sc l v (y.c1) (z.c2)
  | For Value (Dot Name Comp) (Dot Name Comp)      -- ^ for l v (y.c1) (z.c2)
  | Handle Handler Comp                            -- ^ v ★ c
  | Do Name Comp Comp                              -- ^ do x <- c1 in c2
  | Rec Name Comp Comp                             -- ^ rec x c1 c2
  | App Value Value                                -- ^ v1 v2
  | Let Name Value Comp                            -- ^ let x = v in c
  | Letrec Name Value Comp                         -- ^ letrec x = c in c
  -- extensions:
  -- We implement most functions in the paper as built-in functions
  -- because the interpreter doesn't support pattern matching and recursive functions.
  | If Value Comp Comp
  | Case Value Name Comp Name Comp
  | Unop Op1 Value
  | Binop Op2 Value Value
  | Undefined                                     -- ^ undefined
  deriving (Eq)

instance Show Comp where
    show (Return v) = "Return " ++ show v
    show (Op l v (x :. c)) = "op " ++ l ++ " " ++ show v ++ " (" ++ x ++ ". " ++ show c ++ ")"
    show (Sc l v (x :. c1) (y :. c2)) = "sc " ++ l ++ " " ++ show v ++ " (" ++ x ++ ". " ++ show c1 ++ ") (" ++ y ++ ". " ++ show c2 ++ ")"
    show (For v (x :. c1) (y :. c2)) = "for " ++ show v ++ " (" ++ x ++ ". " ++ show c1 ++ ") (" ++ y ++ ". " ++ show c2 ++ ")"
    show (Handle h c) = show h ++ " * " ++ show c
    show (Do x c1 c2) = "do " ++ x ++ " <- (" ++ show c1 ++ "\n in " ++ show c2 ++ ")"
    show (App v1 v2) = show v1 ++ " " ++ show v2
    show (Let x v c) = "let " ++ x ++ " = " ++ show v ++ "\n in " ++ show c
    show (Letrec x v c) = "letrec " ++ x ++ " = " ++ show v ++ "\n in " ++ show c    
    show (If v c1 c2) = "\nif " ++ show v ++ "\n then " ++ show c1 ++ "\n else " ++ show c2
    show (Case v x c1 y c2) = "case " ++ show v ++ " of\n " ++ x ++ " -> " ++ show c1 ++ " \n| " ++ y ++ " -> " ++ show c2
    show (Unop op v) = show op ++ " " ++ show v
    show (Binop op v1 v2) = show op ++ " (" ++ show v1 ++ ") (" ++ show v2 ++ ")"
    show Undefined = "undefined"

infixr 8 #
(#) :: Handler -> Comp -> Comp
h # c = Handle h c

data Op1 
    = Not
    | Neg
    | Head
    | Tail
    | Empty
    | HeadS
    | TailS
    | Fst
    | Snd
    | Close
    | Open
    | Read
    | Newmem
    | FirstFail
    | CartesianProd
    deriving (Show, Eq)

data Op2
    = Add
    | Minus
    | Min
    | Mul
    | Append
    | AppendS
    | ConsS
    | ConcatMap
    | AppendCut
    | ConcatMapCutList
    | Retrieve
    | Update
    | Eq
    | Larger
    | Map
    deriving (Show, Eq)

-- | Memory datatype
newtype Memory s = Mem { runMem :: Name -> Maybe s }
instance Eq (Memory a) where
  x == y = True

instance Show (Memory s) where
  show _ = "<memory>"
instance Functor Memory where
  fmap f (Mem m) = Mem (fmap (fmap f) m)

emptymem :: Memory s
emptymem = Mem $ const Nothing
retrieve :: Name -> Memory s -> s
retrieve x m = case runMem m x of Just s  -> s
                                  Nothing -> error "var undefined"
update :: (Name, s) -> Memory s -> Memory s
update (x, s) m = Mem $ \ y -> if x == y then Just s else runMem m y