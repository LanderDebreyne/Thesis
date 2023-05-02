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
app2 f v1 v2 = DoA "f'" (App f v1) Any $ App (Var "f'" 0) (shiftV 1 v2) -- TODO

-- | Generic Algebraic Operation.
op :: Name -> Value -> ValueType -> Comp
op l x t = OpA l x (DotA "y" t (Return (Var "y" 0)))

-- | Generic Scoped Operation.
sc :: Name -> Value -> Name -> ValueType -> Comp -> ValueType -> Comp
sc l x n vt c t = ScA l x (DotA n vt c) (DotA "z'" t (Return (Var "z'" 0)))

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
      Return . LamA "s" Tint $ DoA "k'" (App (Var "k" 1) (Var "s" 0)) (Tfunction Tint Any) $
                         DoA "s'" (Binop Add (Var "s" 1) (Vint 1)) (Tint) $
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
  ("f", "p", "k", Return . LamA "s" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" (Any) $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any)$
                App (Var "p'" 0) (Var "s" 2)
    , LamA "zs" (Tpair (Any) (Tint)) $ DoA "z" (Unop Fst (Var "zs" 0)) Any $
                 DoA "s'" (Unop Snd (Var "zs" 1)) Tint $
                 DoA "k'" (App (Var "k" 4) (Var "z" 1)) (Tfunction Tint Any) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))



-- | @runInc@ is a macro to help applying the initial count value
runIncT :: Int -> Comp -> Comp
runIncT s c = DoA "c'" (HandleA (UFunction (UFirst UNone)) hIncT c) (Tfunction Tint (Tpair (Tlist Tint) Tint)) $ App (Var "c'" 0) (Vint s)

-- | @cInc@ refers to the @c_inc@ program in Section 2.1
cIncT :: Comp
cIncT = OpA "choose" Vunit (DotA "b" Tbool
        (If (Var "b" 0) (op "inc" Vunit Any) (op "inc" Vunit Any)))

tInc1Gam = Map.fromList([
  ("tIncA", Tint), 
  ("tOnceA", Tpair Tint Tint)])
tInc1Sig = Map.fromList([
  ("inc", Lop "inc" Tunit Tunit), 
  ("choose", Lop "choose" Tunit Tbool)])
tInc1Comp = (HandleA (UList UNone) (hOnceT) (runIncT 0 cIncT))
tInc1 = checkFile tInc1Gam tInc1Sig tInc1Comp (Tlist (Tpair Tint Tint))

tInc2Gam = Map.fromList([
  ("tIncA", Tlist Tint), 
  ("tOnceA", Tint)])
tInc2Comp = runIncT 0 (HandleA (UList UNone) (hOnceT) (cIncT))
tInc2 = checkFile tInc2Gam tInc1Sig tInc2Comp (Tpair (Tlist Tint) Tint)

tInc3Sig = Map.fromList([
  ("inc", Lop "inc" Tunit Tunit), 
  ("choose", Lop "choose" Tunit Tbool),
  ("once", Lsc "once" Tunit Tint)])
tInc3Comp = HandleA (UList UNone) (hOnceT) (runIncT 0 cFwdT)
tInc3 = checkFile tInc1Gam tInc3Sig tInc3Comp (Tlist (Tpair Tint Tint))

cIncForT :: Comp
cIncForT = ForA "for" (Vlist [Vunit, Vunit, Vunit, Vunit]) (DotA "y" Tunit (op "inc" Vunit Any)) (DotA "z" Any (Return (Var "z" 0)))

cFwdT :: Comp
cFwdT = ScA "once" Vunit (DotA "_" Any cIncT) (DotA "x" Tint (OpA "inc" Vunit (DotA "y" Tint
        (DoA "z" (Binop Add (Var "x" 1) (Var "y" 0)) Any $ Return (Var "z" 0)))))

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
      DoA "xs" (App (Var "k" 0) (Vbool True)) (Tlist Any) $
      DoA "ys" (App (Var "k" 1) (Vbool False)) (Tlist Any) $
      Binop Append (Var "xs" 1) (Var "ys" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "once" -> Just ("_", "p", "k",
      DoA "ts" (App (Var "p" 1) Vunit) (Tlist Any) $
      DoA "t" (Unop Head (Var "ts" 0)) (Any) $
      App (Var "k" 2) (Var "t" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMap (Var "z" 0) (Var "k" 1)))


-- | @cOnce@ refers to the @c_once@ program in Section 2.3
cOnceT :: Comp
cOnceT = ScA "once" Vunit (DotA "_" Any (op "choose" Vunit Any))
                        (DotA "b" Tbool (If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails"))))

tOnceGam = Map.fromList([
  ("tOnceA", Tstr)])
tOnceSig = Map.fromList([
  ("choose", Lop "choose" Tunit Tbool),
  ("once", Lsc "once" Tunit Tbool)])
tOnceComp = HandleA (UList UNone) hOnceT cOnceT
tOnce = checkFile tOnceGam tOnceSig tOnceComp (Tlist (TValVar "tOnceA"))


----------------------------------------------------------------

hCutT :: Handler
hCutT = Handler
  "hCut" ["choose", "fail", "cut"] ["call"] []
  ("x", Return . Vret $ Vlist [Var "x" 0])
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return . Vret $ Vlist [])
    "choose" -> Just ("x", "k",
      DoA "xs" (App (Var "k" 0) (Vbool True)) (Tret (Tlist Any)) $
      DoA "ys" (App (Var "k" 1) (Vbool False)) (Tret (Tlist Any)) $
      Binop AppendCut (Var "xs" 1) (Var "ys" 0))
    "cut" -> Just ("_", "k", DoA "x" (App (Var "k" 0) Vunit) (Tflag (Tlist Any)) $ Unop Close (Var "x" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "call" -> Just ("_", "p", "k",
      DoA "x" (App (Var "p" 1) Vunit) (Tret (Tlist Any)) $
      DoA "x'" (Unop Open (Var "x" 0)) (Tret (Tlist Any)) $
      Binop ConcatMapCutList (Var "x'" 0) (Var "k" 2))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMapCutList (Var "z" 0) (Var "k" 1)))


-- | A simple program simulates the behavior of @cOnce@ using @cut@ and @call@.
cCutT :: Comp
cCutT = DoA "b" (sc "call" Vunit "_" Tunit
          (DoA "y" (op "choose" Vunit Tbool) (Tbool) $
          If (Var "y" 0) (DoA "_" (op "cut" Vunit Any) (Any) $ Return (Vbool True))
                         (Return (Vbool False))) Tbool) Tbool $
       If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails"))


tCutGam = Map.fromList([
  ("tCutA", Tstr)])
tCutSig = Map.fromList([
  ("choose", Lop "choose" Tunit Tbool),
  ("cut", Lop "cut" Tunit Tunit),
  ("call", Lsc "call" Tunit Tbool)])
tCutComp = HandleA (URet (UList UNone)) hCutT cCutT

tCut = checkFile tCutGam tCutSig tCutComp (Tret (Tlist (TValVar "tCutA")))


----------------------------------------------------------------

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
        (DoA "y" (App (Var "p" 3) (Vbool False)) (Tsum Any Any) $ app2 exceptMapT (Var "y" 0) (Var "k" 3))
        (app2 exceptMapT (Var "x" 1) (Var "k" 2)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  (lift2fwd ("k", "z", app2 exceptMapT (Var "z" 0) (Var "k" 1)))

-- | @exceptMap@ refers to the @exceptMap@ function in Section 7.3
exceptMapT :: Value
exceptMapT = LamA "z" Any . Return . LamA "k" Any $
  Case (Var "z" 1) "e" (Return (Vsum (Left (Var "e" 0))))
                   "x" (App (Var "k" 1) (Var "x" 0))

-- | @cRaise@ refers to the @_raise@ program in Section 7.3
cRaiseT :: Comp
cRaiseT = DoA "x" (op "inc" Vunit Any) Tint $
         DoA "b" (Binop Larger (Var "x" 0) (Vint 10)) Tbool $
         If (Var "b" 0) (OpA "raise" (Vstr "Overflow") (DotA "y" Any (absurd (Var "y" 0))))
                        (Return (Var "x" 0))

-- | @cCatch@ refers to the @c_catch@ program in Section 7.3
cCatchT :: Comp
cCatchT = sc "catch" (Vstr "Overflow") "b" Tbool (If (Var "b" 0) cRaiseT (Return (Vint 10))) Tint

runIncT2 :: Int -> Comp -> Comp
runIncT2 s c = DoA "c'" (HandleA (UFunction (UFirst UNone)) hIncT c) (Tfunction Tint (Tsum Tstr (Tpair Tint Tint))) $ App (Var "c'" 0) (Vint s)


tCatchGam1 = Map.fromList([
  ("tCatchA", Tint),
  ("tIncA", Tint)])
tCatchSig1 = Map.fromList([
  ("raise", Lop "raise" Tstr Any),
  ("catch", Lsc "catch" Tstr Tint),
  ("inc", Lop "inc" Tunit Tint)])
tCatchComp1 = HandleA (USum UNone UNone) hExceptT (runIncT2 42 cCatchT)
tCatch1 = checkFile tCatchGam1 tCatchSig1 tCatchComp1 (Tsum Tstr (Tpair Tint Tint))

runIncT3 :: Int -> Comp -> Comp
runIncT3 s c = DoA "c'" (HandleA (UFunction (UFirst UNone)) hIncT c) (Tfunction Tint (Tpair (Tsum Tstr Tint) Tint)) $ App (Var "c'" 0) (Vint s)

tCatchComp2 = runIncT3 42 (HandleA (USum UNone UNone) hExceptT cCatchT)
tCatch2 = checkFile tCatchGam1 tCatchSig1 tCatchComp2 (Tpair (Tsum Tstr Tint) Tint)


