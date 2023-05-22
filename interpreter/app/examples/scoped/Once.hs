module Once where

import Syntax
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing

----------------------------------------------------------------
-- Nondeterminism with Once effect (Untyped)

-- | Once effect handler
-- choose calculates all possible results
-- once cuts off computation after first result
hOnce :: Handler
hOnce = Handler
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


-- | Once example program
-- Cuts off computation after first result and results heads in a computation that has two results: heads and tails.
cOnce :: Comp
cOnce = Sc "once" Vunit ("_" :. op "choose" Vunit)
                        ("b" :. If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails")))

-- Handling @cOnce@:
-- >>> evalFile $ hOnce # cOnce
-- Return (Vlist [Vstr "heads"])

----------------------------------------------------------------
-- Typed Once effect

-- | Typed once handler
-- Only returns first result
-- choose calculates all possible results
-- once cuts off computation after first result
hOnceT :: Handler
hOnceT = Handler
  "hOnce" ["choose", "fail"] ["once"] []
  ("x", Return $ Vlist [Var "x" 0])
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return $ Vlist [])
    "choose" -> Just ("x", "k",
      DoA "xs" (App (Var "k" 0) (Vbool True)) (Tlist Any) $
      DoA "ys" (App (Var "k" 1) (Vbool False)) (Tlist Any) $
      Binop Append (Var "xs" 1) (Var "ys" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "once" -> Just ("_", "p", "k",
      DoA "ts" (App (Var "p" 1) Vunit) (Tlist Any) $
      DoA "t" (Unop Head (Var "ts" 0)) Any $
      App (Var "k" 2) (Var "t" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMap (Var "z" 0) (Var "k" 1)))


-- | Typed once example computation
-- Cuts off computation after first result and results heads in a computation that has two results: heads and tails.
cOnceT :: Comp
cOnceT = ScA "once" Vunit (DotA "_" Tunit (opT "choose" Vunit Tbool))
                        (DotA "b" Tbool (If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails"))))

-- | First typed once typechecking example
tOnceGam = Map.empty
tOnceSig = Map.fromList([
  ("choose", Lop "choose" Tunit Tbool),
  ("once", Lsc "once" Tunit Tbool)])
tOnceComp = HandleA (UList UNone) hOnceT cOnceT
tOnce = checkFile tOnceGam tOnceSig tOnceComp (Tlist Tstr)


exOnce = hOnce # cOnce