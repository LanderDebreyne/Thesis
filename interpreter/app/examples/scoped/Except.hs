module Except where

import Syntax
import Evaluation
import Inc
import Shared
import qualified Data.Map as Map
import Typing


----------------------------------------------------------------
-- Exceptions effect (Untyped)

-- Exceptions handler
hExcept :: Handler
hExcept = Handler
  "hExcept" ["raise"] ["catch"] []
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
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  (lift2fwd ("k", "z", app2 exceptMap (Var "z" 0) (Var "k" 1)))



exceptMap :: Value
exceptMap = Lam "z" . Return . Lam "k" $
  Case (Var "z" 1) "e" (Return (Vsum (Left (Var "e" 0))))
                   "x" (App (Var "k" 1) (Var "x" 0))

-- example program that raises an exception
cRaise :: Comp
cRaise = Do "x" (op "inc" Vunit) $
         Do "b" (Binop Larger (Var "x" 0) (Vint 10)) $
         If (Var "b" 0) (Op "raise" (Vstr "Overflow") ("y" :. absurd (Var "y" 0)))
                        (Return (Var "x" 0))

-- example program that catches an exception
cCatch :: Comp
cCatch = sc "catch" (Vstr "Overflow") ("b" :. If (Var "b" 0) cRaise (Return (Vint 10)))

-- example program that raises an exception
cIncr :: Comp
cIncr = Do "x" (op "inc" Vunit) $
       Do "b" (Binop Larger (Var "x" 0) (Vint 10)) $
       If (Var "b" 0) (op "raise" (Vstr "Overflow")) (Return (Var "x" 1))

-- example program that catches an exception
cEx :: Comp
cEx = Do "_" cIncr $
      Do "_" cIncr $
      Do "_" cIncr $
      Return (Vstr "success")

-- example program that catches an exception
cCatch2 :: Comp
cCatch2 = Do "_" (cIncr) $
      sc "catch" (Vstr "Overflow") ("b" :. If (Var "b" 0) cEx (Return (Vstr "fail")))

-- Handling @cCatch@:
-- >>> evalFile $ hExcept # runInc 42 cCatch
-- Return (Vsum (Right (Vpair (Vint 10,Vint 42))))
-- >>> evalFile $ runInc 42 (hExcept # cCatch)
-- Return (Vpair (Vsum (Right (Vint 10)),Vint 43))

-- Handling @cCatch@:
-- >>> evalFile $ hExcept # runInc 1 cCatch2
-- Return Right ("success", 5)
-- >>> evalFile $ runInc 1 (hExcept # cCatch2)
-- Return (Right "success", 5)

-- >>> evalFile $ hExcept # runInc 8 cCatch2
-- Return Right ("fail", 9)
-- >>> evalFile $ runInc 8 (hExcept # cCatch2)
-- Return (Right "fail", 12)

-- >>> evalFile $ hExcept # runInc 42 cCatch2
-- Return Left "Overflow"
-- >>> evalFile $ runInc 42 (hExcept # cCatch2)
-- Return (Left "Overflow", 43)

----------------------------------------------------------------
-- Typed Exception example

-- Typed exception handler
-- Raise, catch and handle exceptions
hExceptT :: Handler
hExceptT = Handler
  "hExcept" ["raise"] ["catch"] []
  ("x", Return $ Vsum (Right (Var "x" 0)))
  (\ oplabel -> case oplabel of
    "raise" -> Just ("e", "_", Return $ Vsum (Left (Var "e" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "catch" -> Just ("e", "p", "k",
      DoA "x" (App (Var "p" 1) (Vbool True)) (Tsum Any Any) $
      -- NOTE: A little different from the paper.
      -- We assume Eq is defined for |String + alpha| for simplicity.
      DoA "b" (Binop Eq (Var "x" 0) (Vsum (Left (Var "e" 3)))) Tbool $
      If (Var "b" 0)
        (DoA "y" (App (Var "p" 3) (Vbool False)) (Tsum Any Any) $ app2T exceptMapT (Var "y" 0) (Var "k" 3))
        (app2T exceptMapT (Var "x" 1) (Var "k" 2)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  (lift2fwd ("k", "z", app2T exceptMapT (Var "z" 0) (Var "k" 1)))

-- typed except map function
exceptMapT :: Value
exceptMapT = LamA "z" Any . Return . LamA "k" Any $
  Case (Var "z" 1) "e" (Return (Vsum (Left (Var "e" 0))))
                   "x" (App (Var "k" 1) (Var "x" 0))

-- Typed example computation raising an exception
cRaiseT :: Comp
cRaiseT = DoA "x'" (opT "inc" Vunit Tint) Tint $
         DoA "b" (Binop Larger (Var "x'" 0) (Vint 10)) Tbool $
         If (Var "b" 0) (OpA "raise" (Vstr "Overflow") (DotA "y" Tunit (absurd (Var "y" 0))))
                        (Return (Var "x'" 1))

-- Typed example computation catching an exception
cCatchT :: Comp
cCatchT = scT "catch" (Vstr "Overflow") "b" Tbool (If (Var "b" 0) cRaiseT (Return (Vint 10))) Tint

-- Typed example computation conditionally raising an exception using Inc effect
cIncrT :: Comp
cIncrT = DoA "x" (opT "inc" Vunit Tint) Tint $
       DoA "b" (Binop Larger (Var "x" 0) (Vint 10)) Tbool $
       If (Var "b" 0) (opT "raise" (Vstr "Overflow") Tint) (Return (Var "x" 1))

-- Typed example computation that may or may not throw an exception
cExT :: Comp
cExT = DoA "_" cIncrT Tint $
      DoA "_" cIncrT Tint $
      DoA "_" cIncrT Tint $
      Return (Vstr "success")

-- First typed exception example
tCatchGam1 = Map.fromList([
  ("tIncA", Tbool)])
tCatchSig1 = Map.fromList([
  ("raise", Lop "raise" Tstr Tint),
  ("catch", Lsc "catch" Tstr Tint),
  ("inc", Lop "inc" Tunit Tunit)])
tCatchComp1 = HandleA (USum UNone UNone) hExceptT (runIncT 42 cCatchT (Tsum Tstr (Tpair Tint Tint)))
tCatch1 = checkFile tCatchGam1 tCatchSig1 tCatchComp1 (Tsum Tstr (Tpair Tint Tint))

-- Second typed exception example
tCatchGam2 = Map.fromList([
  ("tIncA", (Tsum Tstr Tint))])
tCatchComp2 = runIncT 42 (HandleA (USum UNone UNone) hExceptT cCatchT) (Tpair (Tsum Tstr Tint) Tint)
tCatch2 = checkFile tCatchGam2 tCatchSig1 tCatchComp2 (Tpair (Tsum Tstr Tint) Tint)

tCatchSig2 = Map.fromList([
  ("raise", Lop "raise" Tstr Tint),
  ("catch", Lsc "catch" Tstr Tstr),
  ("inc", Lop "inc" Tunit Tint)])

-- Example computation catching exception
cCatch2T :: Comp
cCatch2T = DoA "_" (cIncrT) Tint $
      scT "catch" (Vstr "Overflow") "b" Tbool (If (Var "b" 0) cExT (Return (Vstr "fail"))) Tstr

-- Third typed exception example
tCatchGam3 = Map.fromList([
  ("tIncA", Tstr)])
tCatchComp3 = HandleA (USum UNone UNone) hExceptT (runIncT 1 cCatch2T (Tsum Tstr (Tpair Tstr Tint)))
tCatch3 = checkFile tCatchGam3 tCatchSig2 tCatchComp3 (Tsum Tstr (Tpair Tstr Tint))

-- Fourth typed exception example
tCatchGam4 = Map.fromList([
  ("tIncA", (Tsum Tstr Tstr))])
tCatchComp4 = runIncT 1 (HandleA (USum UNone UNone) hExceptT cCatch2T) (Tpair (Tsum Tstr Tstr) Tint)
tCatch4 = checkFile tCatchGam4 tCatchSig2 tCatchComp4 (Tpair (Tsum Tstr Tstr) Tint)

-- Fifth typed exception example
tCatchComp5 = HandleA (USum UNone UNone) hExceptT (runIncT 8 cCatch2T (Tsum Tstr (Tpair Tstr Tint)))
tCatch5 = checkFile tCatchGam3 tCatchSig2 tCatchComp5 (Tsum Tstr (Tpair Tstr Tint))

-- Sixth typed exception example
tCatchComp6 = runIncT 8 (HandleA (USum UNone UNone) hExceptT cCatch2T) (Tpair (Tsum Tstr Tstr) Tint)
tCatch6 = checkFile tCatchGam4 tCatchSig2 tCatchComp6 (Tpair (Tsum Tstr Tstr) Tint)

-- Seventh typed exception example
tCatchComp7 = HandleA (USum UNone UNone) hExceptT (runIncT 42 cCatch2T (Tsum Tstr (Tpair Tstr Tint)))
tCatch7 = checkFile tCatchGam3 tCatchSig2 tCatchComp7 (Tsum Tstr (Tpair Tstr Tint))

-- Eight typed exception example
tCatchComp8 = runIncT 42 (HandleA (USum UNone UNone) hExceptT cCatch2T) (Tpair (Tsum Tstr Tstr) Tint)
tCatch8 = checkFile tCatchGam4 tCatchSig2 tCatchComp8 (Tpair (Tsum Tstr Tstr) Tint)


exCatch1 = (hExcept # runInc 42 cCatch)
exCatch2 = (runInc 42 (hExcept # cCatch))
exCatch3 = (hExcept # runInc 1 cCatch2)
exCatch4 = (runInc 1 (hExcept # cCatch2))
exCatch5 = (hExcept # runInc 8 cCatch2)
exCatch6 = (runInc 8 (hExcept # cCatch2))
exCatch7 = (hExcept # runInc 42 cCatch2)
exCatch8 = (runInc 42 (hExcept # cCatch2))



