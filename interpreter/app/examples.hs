module Examples where

import Syntax
import Evaluation
import Prelude hiding ((<>))
import Data.Text.IO
import System.Random

----------------------------------------------------------------
-- * Some Auxiliary Functions :

-- | @app2 f v1 v2@ applies the function @f@ to two arguments @v1@ and @v2@.
app2 :: Value -> Value -> Value -> Comp
app2 f v1 v2 = Do "f'" (App f v1) $ App (Var "f'" 0) (shiftV 1 v2)

-- | Generic Algebraic Operation.
op :: Name -> Value -> Comp
op l x = Op l x ("y" :. Return (Var "y" 0))

-- | Generic Scoped Operation.
sc :: Name -> Value -> Dot Name Comp -> Comp
sc l x p = Sc l x p ("z" :. Return (Var "z" 0))

-- | @absurd@ is a function that takes a value and returns an undefined computation.
--   The Undefined computation is used as opposed to the undefined haskell primitive to be able to 
--   print/show intermediate computation steps in the evaluation.
absurd :: Value -> Comp
absurd x = Undefined

----------------------------------------------------------------
-- * Section 2.1 & Section 5: Inc

-- | @hInc@ refers to the @h_inc@ handler in Section 2.1 and Section 5
hInc :: Handler
hInc = Handler
  "hInc" ["inc"] []
  ("x", Return . Lam "s" $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "inc" -> Just ("_", "k",
      Return . Lam "s" $ Do "k'" (App (Var "k" 1) (Var "s" 0)) $
                         Do "s'" (Binop Add (Var "s" 1) (Vint 1)) $
                         App (Var "k'" 1) (Var "s'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                 Do "s'" (Unop Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    ))) 
    Nothing

-- | @runInc@ is a macro to help applying the initial count value
runInc :: Int -> Comp -> Comp
runInc s c = Do "c'" (hInc # c) $ App (Var "c'" 0) (Vint s)

-- | @cInc@ refers to the @c_inc@ program in Section 2.1
cInc :: Comp
cInc = Op "choose" Vunit ("b" :.
        If (Var "b" 0) (op "inc" Vunit) (op "inc" Vunit))

-- Handling @cInc@:
-- >>> evalFile $ hOnce # runInc 0 cInc
-- >>> evalFile $ runInc 0 (hOnce # cInc)
-- Return (Vlist [Vpair (Vint 0,Vint 1),Vpair (Vint 0,Vint 1)])
-- Return (Vpair (Vlist [Vint 0,Vint 1],Vint 2))

cFwd :: Comp
cFwd = Sc "once" Vunit ("_" :. cInc) ("x" :. Op "inc" Vunit ("y" :. 
        Do "z" (Binop Add (Var "x" 1) (Var "y" 0)) $ Return (Var "z" 0)))

-- Handling @cFwd@:
-- >>> evalFile $ hOnce # runInc 0 cFwd
-- Return (Vlist [Vpair (Vint 1,Vint 2)])

----------------------------------------------------------------
-- * Section 2.2 & Section 7.1 : Nondeterminism with Once

-- | @hOnce@ refers to the @h_once@ handler in Section 2.2 & Section 7.1
hOnce :: Handler
hOnce = Handler
  "hOnce" ["choose", "fail"] ["once"]
  ("x", Return $ Vlist [Var "x" 0])
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return $ Vlist [])
    "choose" -> Just ("x", "k",
      Do "xs" (App (Var "k" 0) (Vbool True)) $
      Do "ys" (App (Var "k" 1) (Vbool False)) $
      Binop Append (Var "xs" 1) (Var "ys" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "once" -> Just ("_", "p", "k",
      Do "ts" (App (Var "p" 1) Vunit) $
      Do "t" (Unop Head (Var "ts" 0)) $
      App (Var "k" 2) (Var "t" 0))
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMap (Var "z" 0) (Var "k" 1)))
  Nothing

-- | @failure@ is a wrapper for @fail@ with a polymorphic return type.
-- Defined in Section 7.1
failure :: Comp
failure = Op "fail" Vunit ("y" :. absurd (Var "y" 0))

-- | @cOnce@ refers to the @c_once@ program in Section 2.3
cOnce :: Comp
cOnce = Sc "once" Vunit ("_" :. op "choose" Vunit)
                        ("b" :. If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails")))

-- Handling @cOnce@:
-- >>> evalFile $ hOnce # cOnce
-- Return (Vlist [Vstr "heads"])

----------------------------------------------------------------
-- * Section 7.2 : Nondeterminism with Cut

-- | @hCut@ refers to the @h_cut@ handler in Section 7.2
hCut :: Handler
hCut = Handler
  "hCut" ["choose", "fail", "cut"] ["call"]
  ("x", Return . Vret $ Vlist [Var "x" 0])
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return . Vret $ Vlist [])
    "choose" -> Just ("x", "k",
      Do "xs" (App (Var "k" 0) (Vbool True)) $
      Do "ys" (App (Var "k" 1) (Vbool False)) $
      Binop AppendCut (Var "xs" 1) (Var "ys" 0))
    "cut" -> Just ("_", "k", Do "x" (App (Var "k" 0) Vunit) $ Unop Close (Var "x" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "call" -> Just ("_", "p", "k",
      Do "x" (App (Var "p" 1) Vunit) $
      Do "x'" (Unop Open (Var "x" 0)) $
      Binop ConcatMapCutList (Var "x'" 0) (Var "k" 2))
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMapCutList (Var "z" 0) (Var "k" 1)))
  Nothing

-- | A simple program simulates the behavior of @cOnce@ using @cut@ and @call@.
cCut :: Comp
cCut = Do "b" (sc "call" Vunit ("_" :.
          Do "y" (op "choose" Vunit) $
          If (Var "y" 0) (Do "_" (op "cut" Vunit) $ Return (Vbool True))
                         (Return (Vbool False)))) $
       If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails"))

-- Handling @cCut@:
-- >>> evalFile $ hCut # cCut
-- Return (Vret (Vlist [Vstr "heads"]))

----------------------------------------------------------------
-- * Section 7.3 : Exceptions

-- | @hExcept@ refers to the @h_except@ handler in Section 7.3
hExcept :: Handler
hExcept = Handler
  "hExcept" ["raise"] ["catch"]
  ("x", Return $ Vsum (Right (Var "x" 0)))
  (\ oplabel -> case oplabel of
    "raise" -> Just ("e", "_", Return $ Vsum (Left (Var "e" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "catch" -> Just ("e", "p", "k",
      Do "x" (App (Var "p" 1) (Vbool True)) $
      -- NOTE: A little different from the paper.
      -- We assume Eq is defined for |String + alpha| for simplicity.
      Do "b" (Binop Eq (Var "x" 0) (Vsum (Left (Var "e" 3)))) $
      If (Var "b" 0)
        (Do "y" (App (Var "p" 3) (Vbool False)) $ app2 exceptMap (Var "y" 0) (Var "k" 3))
        (app2 exceptMap (Var "x" 1) (Var "k" 2)))
    _ -> Nothing)
  (lift2fwd ("k", "z", app2 exceptMap (Var "z" 0) (Var "k" 1)))
  Nothing

-- | @exceptMap@ refers to the @exceptMap@ function in Section 7.3
exceptMap :: Value
exceptMap = Lam "z" . Return . Lam "k" $
  Case (Var "z" 1) "e" (Return (Vsum (Left (Var "e" 0))))
                   "x" (App (Var "k" 1) (Var "x" 0))

-- | @cRaise@ refers to the @_raise@ program in Section 7.3
cRaise :: Comp
cRaise = Do "x" (op "inc" Vunit) $
         Do "b" (Binop Larger (Var "x" 0) (Vint 10)) $
         If (Var "b" 0) (Op "raise" (Vstr "Overflow") ("y" :. absurd (Var "y" 0)))
                        (Return (Var "x" 0))

-- | @cCatch@ refers to the @c_catch@ program in Section 7.3
cCatch :: Comp
cCatch = sc "catch" (Vstr "Overflow") ("b" :. If (Var "b" 0) cRaise (Return (Vint 10)))

-- Handling @cCatch@:
-- >>> evalFile $ hExcept # runInc 42 cCatch
-- Return (Vsum (Right (Vpair (Vint 10,Vint 42))))
-- >>> evalFile $ runInc 42 (hExcept # cCatch)
-- Return (Vpair (Vsum (Right (Vint 10)),Vint 43))

----------------------------------------------------------------
-- * Section 7.4 : Local State

-- | @hState@ refers to the @h_state@ handler in Section 7.4
hState :: Handler
hState = Handler
  "hState" ["get", "put"] ["local"]
  ("x", Return . Lam "m" $ Return (Vpair (Var "x" 1, Var "m" 0)))
  (\ oplabel -> case oplabel of
    "get" -> Just ("x", "k",
      Return . Lam "m" $ Do "v" (Binop Retrieve (Var "x" 2) (Var "m" 0)) $
                         Do "k'" (App (Var "k" 2) (Var "v" 0)) $
                         App (Var "k'" 0) (Var "m" 2))
    "put" -> Just ("pa", "k",
      Return . Lam "m" $ Do "k'" (App (Var "k" 1) Vunit) $
                         Do "m'" (Binop Update (Var "pa" 3) (Var "m" 1)) $
                         App (Var "k'" 1) (Var "m'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "local" -> Just ("xv", "p", "k",
      Return . Lam "m" $ Do "x" (Unop Fst (Var "xv" 3)) $
                         Do "v" (Unop Snd (Var "xv" 4)) $
                         Do "um" (Binop Update (Var "xv" 5) (Var "m" 2)) $
                         Do "p'" (App (Var "p" 5) Vunit) $
                         Do "tm" (App (Var "p'" 0) (Var "um" 1)) $
                         Do "t" (Unop Fst (Var "tm" 0)) $
                         Do "m'" (Unop Snd (Var "tm" 1)) $
                         Do "k'" (App (Var "k" 8) (Var "t" 1)) $
                         Do "oldv" (Binop Retrieve (Var "x" 7) (Var "m" 8)) $
                         Do "newm" (Binop Update (Vpair (Var "x" 8, Var "oldv" 0)) (Var "m'" 2)) $
                         App (Var "k'" 2) (Var "newm" 0))
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                 Do "s'" (Unop Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing

-- | @cState@ refers to the @c_state@ program in Section 7.4
cState :: Comp
cState = Do "_" (op "put" (Vpair (Vstr "x", Vint 10))) $
         Do "x1" (sc "local" (Vpair (Vstr "x", Vint 42)) ("_" :. op "get" (Vstr "x"))) $
         Do "x2" (op "get" (Vstr "x")) $
         Return (Vpair (Var "x1" 1, Var "x2" 0))

-- Handling @cState@:
handle_cState :: Comp
handle_cState = Do "m" (Unop Newmem Vunit) $ 
                Do "c" (hState # cState) $
                Do "x" (App (Var "c" 0) (Var "m" 1)) $
                Unop Fst (Var "x" 0)
-- >>> evalFile handle_cState
-- Return (Vpair (Vint 42,Vint 10))

----------------------------------------------------------------
-- * Section 7.5 : Depth-Bounded Search

-- | @hDepth@ refers to the @h_depth@ handler in Section 7.5
hDepth :: Handler
hDepth = Handler
  "hDepth" ["choose", "fail"] ["depth"]
  ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose"   -> Just ("x", "k", Return . Lam "d" $
      Do "b" (Binop Eq (Var "d" 0) (Vint 0)) $
      If (Var "b" 0) (Return (Vlist []))
                     (Do "k1" (App (Var "k" 2) (Vbool True)) $
                      Do "k2" (App (Var "k" 3) (Vbool False)) $
                      Do "d'" (Binop Add (Var "d" 3) (Vint (-1))) $
                      Do "xs" (App (Var "k1" 2) (Var "d'" 0)) $
                      Do "ys" (App (Var "k2" 2) (Var "d'" 1)) $
                      Binop Append (Var "xs" 1) (Var "ys" 0) ))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . Lam "d" $
      Do "p'" (App (Var "p" 2) Vunit) $
      Do "xs" (App (Var "p'" 0) (Var "d'" 4)) $
      Binop ConcatMap (Var "xs" 0) (Lam "v_" $ Do "v" (Unop Fst (Var "v_" 0)) $
                                         Do "k'" (App (Var "k" 5) (Var "v" 0)) $
                                         App (Var "k'" 0) (Var "d" 5)))
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "d" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "d" 2)
    , Lam "vs" $ Binop ConcatMap (Var "vs" 0) (Lam "vd" $
        Do "v" (Unop Fst (Var "vd" 0)) $
        Do "d" (Unop Snd (Var "vd" 1)) $
        Do "k'" (App (Var "k" 5) (Var "v" 1)) $
        App (Var "k'" 0) (Var "d" 1))
    )))
    Nothing

-- | @hDepth2@ is another handler for @depth@.
-- The depth consumed by the scoped computation is also counted in the global depth bound.
hDepth2 :: Handler
hDepth2 = Handler
  "hDepth" ["choose", "fail"] ["depth"]
  ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose"   -> Just ("x", "k", Return . Lam "d" $
      Do "b" (Binop Eq (Var "d" 0) (Vint 0)) $
      If (Var "b" 0) (Return (Vlist []))
                     (Do "k1" (App (Var "k" 2) (Vbool True)) $
                      Do "k2" (App (Var "k" 3) (Vbool False)) $
                      Do "d'" (Binop Add (Var "d" 3) (Vint (-1))) $
                      Do "xs" (App (Var "k1" 2) (Var "d'" 0)) $
                      Do "ys" (App (Var "k2" 2) (Var "d'" 1)) $
                      Binop Append (Var "xs" 1) (Var "ys" 0) ))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . Lam "d" $
      Do "p'" (App (Var "p" 2) Vunit) $
      Do "md" (Binop Min (Var "d'" 4) (Var "d" 1)) $
      Do "xs" (App (Var "p'" 1) (Var "md" 0)) $
      Binop ConcatMap (Var "xs" 0) (Lam "vd" $ Do "v" (Unop Fst (Var "vd" 0)) $
                                         Do "rd" (Unop Snd (Var "vd" 1)) $
                                         Do "consumed" (Binop Minus (Var "md" 4) (Var "rd" 0)) $
                                         Do "trued" (Binop Minus (Var "d" 7) (Var "consumed" 0)) $
                                         Do "k'" (App (Var "k" 9) (Var "v" 3)) $
                                         App (Var "k'" 0) (Var "trued" 1)))
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "d" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "d" 2)
    , Lam "vs" $ Binop ConcatMap (Var "vs" 0) (Lam "vd" $
        Do "v" (Unop Fst (Var "vd" 0)) $
        Do "d" (Unop Snd (Var "vd" 1)) $
        Do "k'" (App (Var "k" 5) (Var "v" 1)) $
        App (Var "k'" 0) (Var "d" 1))
    )))
    Nothing

-- | @cDepth@ refers to the @c_depth@ program in Section 7.5
cDepth :: Comp
cDepth = Sc "depth" (Vint 1) ("_" :.
 Do "b" (op "choose" Vunit) $
 If (Var "b" 0) (Return (Vint 1))
                ( Do "b'" (op "choose" Vunit) $
                  If (Var "b'" 0)
                     (Return (Vint 2))
                     (Return (Vint 3))))
  ("x" :.
   Do "b" (op "choose" Vunit) $
   If (Var "b" 0) (Return (Var "x" 1))
                  ( Do "b'" (op "choose" Vunit) $
                    If (Var "b'" 0)
                       (Return (Vint 4))
                       (Do "b''" (op "choose" Vunit) $
                         If (Var "b''" 0)
                            (Return (Vint 5))
                            (Return (Vint 6)))))

-- Handling @cDepth@:
-- >>> evalFile $ Do "f" (hDepth # cDepth) $ App (Var "f" 0) (Vint 2)
-- Return (Vlist [Vpair (Vint 1,Vint 1),Vpair (Vint 4,Vint 0)])
-- >>> evalFile $ Do "f" (hDepth2 # cDepth) $ App (Var "f" 0) (Vint 2)
-- Return (Vlist [Vpair (Vint 1,Vint 0)])

----------------------------------------------------------------
-- * Section 7.6 : Parsers

-- | @hToken@ refers to the @h_token@ handler in Section 7.6
hToken :: Handler
hToken = Handler
  "hToken" ["token"] []
  ("x", Return . Lam "s" $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "token" -> Just ("x", "k", Return . Lam "s" $
      Do "b" (Binop Eq (Var "s" 0) (Vstr "")) $
      If (Var "b" 0) failure
                     ( Do "x'" (Unop HeadS (Var "s" 1)) $
                       Do "xs" (Unop TailS (Var "s" 2)) $
                       Do "b" (Binop Eq (Var "x" 5) (Var "x'" 1)) $
                       If (Var "b" 0) (app2 (Var "k" 5) (Var "x" 6) (Var "xs" 1)) failure))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                 Do "s'" (Unop Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing

-- | @<>@ refers to the syntactic sugar @<>@ in Section 7.6
(<>) :: Comp -> Comp -> Comp
x <> y = Op "choose" Vunit ("b" :. If (Var "b" 0) (shiftC 1 x) (shiftC 1 y))

-- Parsers defined in Fig. 7 :
digit :: Value
digit =  Lam "_" $ 
         op "token" (Vchar '0')
      <> op "token" (Vchar '1')
      <> op "token" (Vchar '2')
      <> op "token" (Vchar '3')
      <> op "token" (Vchar '4')
      <> op "token" (Vchar '5')
      <> op "token" (Vchar '6')
      <> op "token" (Vchar '7')
      <> op "token" (Vchar '8')
      <> op "token" (Vchar '9')
-- | For simplicity, we directly use Haskell's recursion to implement the recursive function @many1@.
many1 :: Value -> Comp
many1 p = Do "a" (App p Vunit) $
          Do "as" (many1 p <> Return (Vstr "")) $
          Do "x" (Binop ConsS (Var "a" 1) (Var "as" 0)) $
          Return (Var "x" 0)
expr :: Value
expr = Lam "_" $
       (Do "i" (App term Vunit) $
        Do "_" (op "token" (Vchar '+')) $
        Do "j" (App expr Vunit) $
        Do "x" (Binop Add (Var "i" 2) (Var "j" 0)) $
        Return (Var "x" 0))
    <> (Do "i" (App term Vunit) $ Return (Var "i" 0))
term :: Value
term = Lam "_" $
       (Do "i" (App factor Vunit) $
        Do "_" (op "token" (Vchar '*')) $
        Do "j" (App term Vunit) $
        Do "x" (Binop Mul (Var "i" 2) (Var "j" 0)) $
        Return (Var "x" 0))
    <> (Do "i" (App factor Vunit) $ Return (Var "i" 0))
factor :: Value
factor = Lam "_" $
         (Do "ds" (many1 digit) $
          Do "x" (Unop Read (Var "ds" 0)) $
          Return (Var "x" 0))
      <> (Do "_" (op "token" (Vchar '(')) $
          Do "i" (App expr Vunit) $
          Do "_" (op "token" (Vchar ')')) $
          Return (Var "i" 1))

-- | @expr1@ refers to the @expr_1@ parser in Section 7.6
expr1 :: Value
expr1 = Lam "_" $
        Do "i" (App term Vunit) $
        sc "call" Vunit ("_" :. ( Do "_" (op "token" (Vchar '+')) $
                                  Do "_" (op "cut" Vunit) $
                                  Do "j" (App expr1 Vunit) $
                                  Do "x" (Binop Add (Var "i" 4) (Var "j" 0)) $
                                  Return (Var "x" 0)) <> Return (Var "i" 1))


-- Handling @expr1@:
handle_expr1 :: Comp
handle_expr1 = hCut # (Do "c" (hToken # App expr1 Vunit) $
                       App (Var "c" 0) (Vstr "(2+5)*8"))
-- >>> evalP $ handle_expr1
-- Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")]))

-- Handling @expr@:
handle_expr :: Comp
handle_expr = hCut # (Do "c" (hToken # App expr Vunit) $
                      App (Var "c" 0) (Vstr "(2+5)*8"))
-- >>> evalP $ handle_expr
-- Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")]))

----------------------------------------------------------------
-- Reader effect
-- ask algebraic effect
-- local scoped effect

-- | @hReader@ is a reader handler
hReader :: Handler
hReader = Handler
  "hReader" ["ask"] ["local"]
  ("x", Return . Lam "m" $ Return (Vpair (Var "x" 1, Var "m" 0)))
  (\ oplabel -> case oplabel of
    "ask" -> Just ("_", "k",
      Return . Lam "m" $ Do "env" (Binop Retrieve (Vstr "readerEnv") (Var "m" 0)) $
                         Do "k'" (App (Var "k" 2) (Var "env" 0)) $
                         App (Var "k'" 0) (Var "m" 2))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "local" -> Just ("x", "p", "k",
      Return . Lam "m" $ Do "envKey" (Return (Vstr "readerEnv")) $
                         Do "oldEnv" (Binop Retrieve (Var "envKey" 0) (Var "m" 1)) $
                         Do "newEnv" (App (Var "x" 5) (Var "oldEnv" 0)) $ 
                         Do "um" (Binop Update (Vpair ((Var "envKey" 2), (Var "newEnv" 0))) (Var "m" 3)) $
                         Do "p'" (App (Var "p" 6) Vunit) $
                         Do "tm" (App (Var "p'" 0) (Var "um" 1)) $
                         Do "t" (Unop Fst (Var "tm" 0)) $
                         Do "m'" (Unop Snd (Var "tm" 1)) $
                         Do "k'" (App (Var "k" 9) (Var "t" 1)) $
                         Do "newm" (Binop Update (Vpair ((Var "envKey" 8), (Var "oldEnv" 7))) (Var "m'" 1)) $
                         App (Var "k'" 1) (Var "newm" 0))
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                 Do "s'" (Unop Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing

-- | cReader is an example reader effect program
cReader :: Comp
cReader = Do "x1" (op "ask" Vunit) $
          Do "x2" ((sc "local" (Lam "x" (Binop Append (Var "x" 0) (Vlist [Vint 5])))) ("_" :. op "ask" Vunit)) $
          Do "x3" (op "ask" Vunit) $ 
          Return (Vpair ((Vpair (Var "x1" 0, Var "x3" 1)), (Var "x3" 2)))

-- | @runReader@ is a macro to help applying the initial reader value
runReader :: Value -> Comp -> Comp
runReader s c = Do "x3" ((sc "local" s) ("_" :. c)) $ 
                Return (Var "x3" 0)

-- Handling @cReader@:
handle_cReader :: Value -> Comp
handle_cReader c = Do "m" (Unop Newmem (Vunit)) $
                   Do "c" (hReader # (runReader (c) cReader)) $
                   Do "x" (App (Var "c" 0) (Var "m" 1)) $
                   Unop Fst (Var "x" 0)

-- @cReader@ example:
example_cReader :: Comp
example_cReader = handle_cReader (Lam "x" (Return (Vlist [(Vint 1), (Vint 2), (Vint 3), (Vint 4)])))

-- Usage:
-- >>> evalP $ example_cReader
-- Return (Vpair (Vpair (Vlist [Vint 1,Vint 2,Vint 3,Vint 4],Vlist [Vint 1,Vint 2,Vint 3,Vint 4,Vint 5]),Vlist [Vint 1,Vint 2,Vint 3,Vint 4]))

----------------------------------------------------------------
-- Parallel example 

-- | @hAccum@ is an example handler for accumulating a value
hAccum :: Handler
hAccum = Handler
  "hAccum" ["accum"] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    (Just ("list", "l", "k", 
      Do "pairs" (App (Var "l" 1) (Var "list" 2)) $
      Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
      Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
      Do "k'" (App (Var "k" 3) (Var "second" 0)) $
      Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
                                 If (Var "n" 0) (Return (Vint 0)) (Do "h" (Unop Head (Var "l" 1)) $
                                                                   Do "t" (Unop Tail (Var "l" 2)) $
                                                                   Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                                   Do "x" (Binop Add (Var "h" 2) (Var "y" 0)) $
                                                                   Return (Var "x" 0))) 
        (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
        Do "base" (Unop Fst (Var "k'" 2)) $
        Do "k''" (Unop Snd (Var "k'" 3)) $
        Do "res" (Binop Add (Var "base" 1) (Var "rest" 2)) $
        Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))

hPure :: Handler
hPure = Parallel
  (("list", "p", "k", 
      Do "result" (Binop Map (Var "list" 2) (Var "p" 1)) $
      App (Var "k" 1) (Var "result" 0)))
  (("x", Return (Var "x" 0)))

cAccum :: Comp
cAccum = For (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5]) ("y" :. (op "accum" (Var "y" 0))) ("z" :. (Return (Var "z" 0)))

exFor :: Comp
exFor = hPure # hAccum # cAccum

-- Usage:
-- >>> evalFile $ exFor
-- Return (VPair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit]))


-- Example without traverse clausule

hAccumNoFor :: Handler
hAccumNoFor = Handler
  "hAccum" ["accum"] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing

exNoFor :: Comp
exNoFor = hPure # hAccumNoFor # cAccum

-- Each element of the list is treated as a separate computation
-- The result is a list of results of each computation
-- The results are not accumulated

-- Usage:
-- >>> evalFile $ exNoFor
-- Return (0, [(1, ()),(2, ()),(3, ()),(4, ()),(5, ())])

----------------------------------------------------------------
-- Weak exceptions example

-- Ideally does not need separate handler for accumulating strings
hAccumS :: Handler
hAccumS = Handler
  "hAccum" ["accum"] []
  ("x", Return (Vpair (Vstr "", Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop AppendS (Var "x" 4) (Var "m'" 1)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    (Just ("list", "l", "k", 
      Do "pairs" (App (Var "l" 1) (Var "list" 2)) $
      Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
      Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
      Do "k'" (App (Var "k" 3) (Var "second" 0)) $
      Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
                            If (Var "n" 0) (Return (Vstr "")) (Do "h" (Unop Head (Var "l" 1)) $
                                                              Do "t" (Unop Tail (Var "l" 2)) $
                                                              Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                              Do "x" (Binop AppendS (Var "h" 2) (Var "y" 0)) $
                                                              Return (Var "x" 0))) 
        (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
        Do "base" (Unop Fst (Var "k'" 2)) $
        Do "k''" (Unop Snd (Var "k'" 3)) $
        Do "res" (Binop AppendS (Var "base" 1) (Var "rest" 2)) $
        Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))

hWeak :: Handler
hWeak = Handler
  "hWeak" ["throw"] []
  ("x", Return (Vsum (Right (Var "x" 0))))
  (\ oplabel -> case oplabel of
    "throw" -> Just ("x", "k", Return (Vsum (Left (Var "x" 1))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    (Just ("list", "l", "k",
      Do "results" (App (Var "l" 1) (Var "list" 2)) $ 
      Do "FirstFail" (Unop FirstFail (Var "results" 0)) $
      Case (Var "FirstFail" 0) 
        "error" (Return $ Vsum $ Left (Var "error" 0))
        "t" (App (Var "k" 3) (Var "t" 0))
    ))


cWeak = Do "_" (Op "accum" (Vstr "start ") ("y" :. Return (Var "y" 0))) $ 
         (For (Vlist [Vstr "1", Vstr "2", Vstr "3", Vstr "4", Vstr "5"])
         ("x" :. (Do "eq2" (Binop Eq (Var "x" 0) (Vstr "2")) $
         If (Var "eq2" 0)   (Do "_" (Op "accum" (Vstr "!") ("y" :. Return (Var "y" 0))) $
                            Do "_" (Op "throw" (Vstr "error") ("y" :. Return (Var "y" 0))) $
                            Op "accum" (Vstr "unreachable") ("y" :. Return (Var "y" 0)))
        (Op "accum" (Var "x" 1) ("y" :. Return (Var "y" 0)))))
        ("x" :. Return (Var "x" 0)))

exWeak = hPure # hAccumS # hWeak # cWeak

-- Usage:
-- >>> evalFile $ exWeak
-- Return ("start 1!345", Left "error")


----------------------------------------------------------
-- PRNG example

hPRNG :: Handler
hPRNG = Handler
  "hPRNG" ["sampleUniform"] []
  ("x", Return . Lam "key" $ Return (Var "x" 1))
  (\ oplabel -> case oplabel of
    "sampleUniform" -> Just ("x", "k", Return . Lam "key" $ 
      Do "pair" (Unop Rand (Var "key" 0)) $
      Do "val" (Unop Fst (Var "pair" 0)) $
      Do "key" (Unop Snd (Var "pair" 1)) $
      Do "cont" (App (Var "k" 4) (Var "val" 1)) $ 
      App (Var "cont" 0) (Var "key" 1))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
  ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
  , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
              Do "s'" (Unop Snd (Var "zs" 1)) $
              Do "k'" (App (Var "k" 4) (Var "z" 1)) $
              App (Var "k'" 0) (Var "s'" 1)
  )))
  (Just ("list", "l", "k", Return . Lam "key" $ 
    Do "keys" (Unop SplitKeyPair (Var "key" 0)) $
    Do "key1" (Unop Fst (Var "keys" 0)) $
    Do "key2" (Unop Snd (Var "keys" 1)) $
    Do "key1s" (Binop SplitKey (Var "key1" 1) (Var "list" 6)) $
    Do "for" (App (Var "l" 6) (Var "list" 7)) $
    Do "results" (Binop Zip (Var "for" 0) (Var "key1s" 1)) $
    Do "cont" (App (Var "k" 7) (Var "results" 0)) $
    App (Var "cont" 0) (Var "key2" 4)))


cPRNG :: Comp
cPRNG = For (Vlist [Vunit, Vunit, Vunit]) ("y" :. Op "sampleUniform" (Vunit) ("y" :. Return (Var "y" 0))) ("y" :. Return (Var "y" 0))

cPRNGseq :: Comp
cPRNGseq =  Do "1" (Op ("sampleUniform") (Vunit) ("y" :. Return (Var "y" 0))) $
            Do "2" (Op ("sampleUniform") (Vunit) ("y" :. Return (Var "y" 0))) $
            Do "3" (Op ("sampleUniform") (Vunit) ("y" :. Return (Var "y" 0))) $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

-- Needs new parallel handler to thread keys through correctly
hPureK :: Handler
hPureK = Parallel
  (("list", "p", "k", Return . Lam "keys" $
      Do "results" (Binop Map (Var "list" 2) (Var "p" 1)) $
      Do "resultskeys" (Binop Map (Var "results" 0) (Var "keys" 1)) $
      App (Var "k" 3) (Var "resultskeys" 0)))
  (("x", Return (Var "x" 0)))

exPRNGpar :: Comp
exPRNGpar = hPure # (Do "key" (Return (Vkey (mkStdGen 42))) $
         Do "ex" (hPureK # hPRNG # cPRNG) $
        (App (Var "ex" 0) (Var "key" 1)))

exPRNGseq :: Comp
exPRNGseq = hPure # (Do "key" (Return (Vkey (mkStdGen 42))) $
         Do "ex" (hPure # hPRNG # cPRNGseq) $
        (App (Var "ex" 0) (Var "key" 1)))


-- Usage:
-- Parallel version
-- >>> evalFile $ exPRNGpar
-- Return [80, 38, 7]
-- Sequential version
-- >>> evalFile $ exPRNGseq
-- Return [48, 23, 95]

-- Notice different values, because the keys split in the parallel version

----------------------------------------------------------
-- Amb example

hAmb :: Handler
hAmb = Handler
  "hAmb" ["amb"][]
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    "amb" -> Just ("x", "k",
      For (Var "x" 1) ("y" :. App (Var "k" 1) (Var "y" 0)) ("z" :. Return (Var "z" 0)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
  ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
  , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
              Do "s'" (Unop Snd (Var "zs" 1)) $
              Do "k'" (App (Var "k" 4) (Var "z" 1)) $
              App (Var "k'" 0) (Var "s'" 1)
  )))
  (Just ("list", "l", "k",
    Do "results" (App (Var "l" 1) (Var "list" 2)) $ 
    Do "productElts" (Unop CartesianProd (Var "results" 0)) $
    For (Var "productElts" 0) ("y" :. App (Var "k" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))
  ))

cAmb :: Comp
cAmb = 
  Do "d1" (Op "amb" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5, Vint 6, Vint 7, Vint 8, Vint 9]) ("y" :. Return (Var "y" 0))) $
  Do "d2" (Op "amb" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5, Vint 6, Vint 7, Vint 8, Vint 9]) ("y" :. Return (Var "y" 0))) $
  Do "res" (Binop Add (Var "d1" 1) (Var "d2" 0)) $
  Do "eq" (Binop Eq (Var "res" 0) (Vint 13)) $
  If (Var "eq" 0) (Op "accum" (Vint 1) ("y" :. Return Vunit)) (Return Vunit)


exAmb :: Comp
exAmb = hPure # hAccum # hAmb # cAmb

-- Usage:
-- >>> evalFile $ exAmb
-- Return (6, [[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()]])

-- Finds [(4,9),(5,8),(6,7),(7,6),(8,5),(9,4)]


cComb :: Comp
cComb = 
  Do "d1" (Op "amb" (Vlist [Vstr "H", Vstr "T"]) ("y" :. Return (Var "y" 0))) $
  Do "d2" (Op "amb" (Vlist [Vstr "H", Vstr "T"]) ("y" :. Return (Var "y" 0))) $
  Do "d3" (Op "amb" (Vlist [Vstr "H", Vstr "T"]) ("y" :. Return (Var "y" 0))) $
  Do "l1" (Binop AppendS (Var "d1" 2) (Var "d2" 1)) $ 
  Binop AppendS (Var "l1" 0) (Var "d3" 1)

exComb :: Comp
exComb = hPure # hAmb # cComb

-- Usage:
-- >>> evalFile $ exComb
-- Return [[["HHH","HHT"],["HTH","HTT"]],[["THH","THT"],["TTH","TTT"]]]

----------------------------------------------------------

-- Parallel (accum) example via scoped effect

hAccumSc1 :: Handler
hAccumSc1 = Handler
  "hAccumSc" ["accum"] ["for"]
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "pairs" (Sc "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
              Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
              Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
              Do "k'" (App (Var "k" 3) (Var "second" 0)) $
              Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
              If (Var "n" 0) (Return (Vint 0)) (Do "h" (Unop Head (Var "l" 1)) $
                                                Do "t" (Unop Tail (Var "l" 2)) $
                                                Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                Do "x" (Binop Add (Var "h" 2) (Var "y" 0)) $
                                                Return (Var "x" 0))) 
              (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
              Do "base" (Unop Fst (Var "k'" 2)) $
              Do "k''" (Unop Snd (Var "k'" 3)) $
              Do "res" (Binop Add (Var "base" 1) (Var "rest" 2)) $
              Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing


hAccumSc2 :: Handler
hAccumSc2 = Handler
  "hAccumSc" ["accum"] ["for"]
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "pairs" (For (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
              Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
              Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
              Do "k'" (App (Var "k" 3) (Var "second" 0)) $
              Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
              If (Var "n" 0) (Return (Vint 0)) (Do "h" (Unop Head (Var "l" 1)) $
                                                Do "t" (Unop Tail (Var "l" 2)) $
                                                Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                Do "x" (Binop Add (Var "h" 2) (Var "y" 0)) $
                                                Return (Var "x" 0))) 
              (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
              Do "base" (Unop Fst (Var "k'" 2)) $
              Do "k''" (Unop Snd (Var "k'" 3)) $
              Do "res" (Binop Add (Var "base" 1) (Var "rest" 2)) $
              Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing


hPureSc :: Handler
hPureSc = Handler
  "hPureSc" [] ["for"]
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "results" (Binop Map (Var "x" 2) (Var "p" 1)) $
              App (Var "k" 1) (Var "results" 0))
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing


-- cAccum example rewritten as scoped effect
cAccumSc :: Comp
cAccumSc = Sc "for" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5]) ("y" :. (op "accum" (Var "y" 0))) ("z" :. (Return (Var "z" 0)))

-- cAccumSc example handled by handler that uses scoped effect for pure for handling
exForSc1 :: Comp
exForSc1 = hPureSc # hAccumSc1 # cAccumSc

-- Usage:
-- evalFile exForSc1
-- Return (15, [(),(),(),(),()])

-- cAccumSc example handled by handler that uses parallel effect for pure for handling
exForSc2 :: Comp
exForSc2 = hPure # hAccumSc2 # cAccumSc

-- Usage:
-- evalFile exForSc2
-- Return (15, [(),(),(),(),()])

-- Remark that all cAccum examples find the same solution

----------------------------------------------------------------------------------------------------------------------------

-- Weak exceptions example as scoped effect

-- Ideally does not need separate handler for accumulating strings
hAccumSSc :: Handler
hAccumSSc = Handler
  "hAccumSc" ["accum"] ["for"]
  ("x", Return (Vpair (Vstr "", Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop AppendS (Var "x" 4) (Var "m'" 1)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "pairs" (Sc "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
              Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
              Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
              Do "k'" (App (Var "k" 3) (Var "second" 0)) $
              Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
                                    If (Var "n" 0) (Return (Vstr "")) (Do "h" (Unop Head (Var "l" 1)) $
                                                                      Do "t" (Unop Tail (Var "l" 2)) $
                                                                      Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                                      Do "x" (Binop AppendS (Var "h" 2) (Var "y" 0)) $
                                                                      Return (Var "x" 0))) 
                (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
                Do "base" (Unop Fst (Var "k'" 2)) $
                Do "k''" (Unop Snd (Var "k'" 3)) $
                Do "res" (Binop AppendS (Var "base" 1) (Var "rest" 2)) $
                Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing


hWeakSc :: Handler
hWeakSc = Handler
  "hWeak" ["throw"] ["for"]
  ("x", Return (Vsum (Right (Var "x" 0))))
  (\ oplabel -> case oplabel of
    "throw" -> Just ("x", "k", Return (Vsum (Left (Var "x" 1))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k",
      Do "results" (Sc "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
      Do "FirstFail" (Unop FirstFail (Var "results" 0)) $
      Case (Var "FirstFail" 0) 
        "error" (Return $ Vsum $ Left (Var "error" 0))
        "t" (App (Var "k" 3) (Var "t" 0)))
    _ -> Nothing)
  ("f", "p", "k", App (Var "f" 3) (Vpair -- TODO fwd
    ( Lam "y" $ (App (Var "p" 3) (Var "y" 0))
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                Do "s'" (Unop Snd (Var "zs" 1)) $
                Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                App (Var "k'" 0) (Var "s'" 1)
    )))
    Nothing

cWeakSc :: Comp
cWeakSc = Do "_" (Op "accum" (Vstr "start ") ("y" :. Return (Var "y" 0))) $ 
         (Sc "for" (Vlist [Vstr "1", Vstr "2", Vstr "3", Vstr "4", Vstr "5"])
         ("x" :. (Do "eq2" (Binop Eq (Var "x" 0) (Vstr "2")) $
         If (Var "eq2" 0)   (Do "_" (Op "accum" (Vstr "!") ("y" :. Return (Var "y" 0))) $
                            Do "_" (Op "throw" (Vstr "error") ("y" :. Return (Var "y" 0))) $
                            Op "accum" (Vstr "unreachable") ("y" :. Return (Var "y" 0)))
        (Op "accum" (Var "x" 1) ("y" :. Return (Var "y" 0)))))
        ("x" :. Return (Var "x" 0)))

exWeakSc :: Comp
exWeakSc = hPureSc # hAccumSSc # hWeakSc # cWeakSc

-- Usage:
-- >>> evalFile exWeakSc
-- Return ("start 1!345", Left "error")