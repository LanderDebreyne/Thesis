module Cut where

import Syntax
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing

----------------------------------------------------------------
-- Nondeterminism with Cut Effect (Untyped)

-- | Cut effect handler
-- choose calculates all possible results
-- cut cuts off computation after first result
-- call calls a scoped computation (containing cut)
hCut :: Handler
hCut = Handler
  "hCut" ["choose", "fail", "cut"] ["call"] []
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
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMapCutList (Var "z" 0) (Var "k" 1)))


-- | A simple program that simulates the behavior of @cOnce@ using @cut@ and @call@.
-- Cuts off computation after first result and results heads in a computation that has two results: heads and tails.
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
-- Typed Cut effect

-- | Typed cut handler
-- choose calculates all possible results
-- cut cuts off computation after first result
-- call calls a scoped computation (containing cut)
hCutT :: Handler
hCutT = Handler
  "hCut" ["choose", "fail", "cut"] ["call"] []
  ("x", Return . Vret $ Vlist [Var "x" 0])
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return . Vret $ Vlist [])
    "choose" -> Just ("x", "k",
      DoA "xs" (App (Var "k" 0) (Vbool True)) (Tret (Tlist (TVar "tCutA"))) $
      DoA "ys" (App (Var "k" 1) (Vbool False)) (Tret (Tlist (TVar "tCutA"))) $
      Binop AppendCut (Var "xs" 1) (Var "ys" 0))
    "cut" -> Just ("_", "k", DoA "x" (App (Var "k" 0) Vunit) (Tflag (Tlist (TVar "tCutA"))) $ Unop Close (Var "x" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "call" -> Just ("_", "p", "k",
      DoA "x" (App (Var "p" 1) Vunit) (Tret (Tlist (TVar "tCutA"))) $
      DoA "x'" (Unop Open (Var "x" 0)) (Tret (Tlist (TVar "tCutA"))) $
      Binop ConcatMapCutList (Var "x'" 0) (Var "k" 2))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMapCutList (Var "z" 0) (Var "k" 1)))


-- | Typed cut effect example computation
-- Cuts off computation after first result and results heads in a computation that has two results: heads and tails.
cCutT :: Comp
cCutT = DoA "b" (scT "call" Vunit "_" Tunit
          (DoA "y" (opT "choose" Vunit Tbool) (Tbool) $
          If (Var "y" 0) (DoA "_" (opT "cut" Vunit Tunit) Tunit $ Return (Vbool True))
                         (Return (Vbool False))) Tbool) Tbool $
       If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails"))


-- | Typed cut effect typechecking example
tCutGam = Map.fromList([
  ("tCutA", Tbool)])
tCutSig = Map.fromList([
  ("choose", Lop "choose" Tunit Tbool),
  ("cut", Lop "cut" Tunit Tunit),
  ("call", Lsc "call" Tunit Tbool)])
tCutComp = HandleA (URet (UList UNone)) hCutT cCutT

tCut = checkFile tCutGam tCutSig tCutComp (Tret (Tlist Tstr))


exCut = hCut # cCut