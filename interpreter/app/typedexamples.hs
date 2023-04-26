module TypedExamples where

import Syntax
import Evaluation
import Prelude hiding ((<>))
import Data.Text.IO
import System.Random
import qualified Data.Set as Set
import qualified Data.Map as Map
import Typing

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
absurd _ = Undefined

----------------------------------------------------------------
-- * Section 2.1 & Section 5: Inc

-- | @hInc@ refers to the @h_inc@ handler in Section 2.1 and Section 5
hIncT :: Handler
hIncT = Handler
  "hInc" ["inc"] [] []
  ("x", Return . LamA "s" Tint $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "inc" -> Just ("_", "k",
      Return . LamA "s" Tint $ Do "k'" (App (Var "k" 1) (Var "s" 0)) $
                         Do "s'" (Binop Add (Var "s" 1) (Vint 1)) $
                         App (Var "k'" 1) (Var "s'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" ->   (Just ("list", "l", "k", Return . Lam "s" $ 
          Do "xs" (App (Var "l" 2) (Var "list" 3)) $
          Do "first" (Binop Map (Var "xs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
          Do "second" (Binop Map (Var "xs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
          Do "k'" (App (Var "k" 4) (Var "first" 1)) $
          Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
                                    If (Var "n" 0) (Return (Vint 0)) 
                                    (Do "h" (Unop Head (Var "l" 1)) $
                                      Do "t" (Unop Tail (Var "l" 2)) $
                                      Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                      Do "x" (Binop Add (Var "h" 2) (Var "y" 0)) $
                                      Return (Var "x" 0))) 
            (Do "s'" (App (Var "reduce" 0) (Var "second" 2)) $
            App (Var "k'" 2) (Var "s'" 0))))
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                 Do "s'" (Unop Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))



-- | @runInc@ is a macro to help applying the initial count value
runIncT :: Int -> Comp -> Comp
runIncT s c = DoA "c'" (HandleA (THandler (Tint, Set.empty) (Tint, Set.empty)) hIncT c) (Tfunction Tint (Tpair Tunit Tint, Set.empty), Set.empty) $ App (Var "c'" 0) (Vint s)

-- | @cInc@ refers to the @c_inc@ program in Section 2.1
cIncT :: Comp
cIncT = Op "choose" Vunit ("b" :.
        If (Var "b" 0) (op "inc" Vunit) (op "inc" Vunit))

cIncForT :: Comp
cIncForT = For "for" (Vlist [Vunit, Vunit, Vunit, Vunit]) ("y" :. op "inc" Vunit) ("z" :. Return (Var "z" 0))

testIncT = checkFile (HandleA (THandler (Tpair Tunit Tint, Set.empty) (Tunit, Set.empty)) (hOnceT) (runIncT 0 cIncT)) (Tunit, Set.empty)

cFwdT :: Comp
cFwdT = Sc "once" Vunit ("_" :. cIncT) ("x" :. Op "inc" Vunit ("y" :. 
        Do "z" (Binop Add (Var "x" 1) (Var "y" 0)) $ Return (Var "z" 0)))

----------------------------------------------------------------
-- * Section 2.2 & Section 7.1 : Nondeterminism with Once

-- | @hOnce@ refers to the @h_once@ handler in Section 2.2 & Section 7.1
hOnceT :: Handler
hOnceT = Handler
  "hOnce" ["choose", "fail"] ["once"] []
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
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMap (Var "z" 0) (Var "k" 1)))


-- | @cOnce@ refers to the @c_once@ program in Section 2.3
cOnceT :: Comp
cOnceT = Sc "once" Vunit ("_" :. op "choose" Vunit)
                        ("b" :. If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails")))

-- Handling @cOnce@:
-- >>> evalFile $ hOnce # cOnce
-- Return (Vlist [Vstr "heads"])
