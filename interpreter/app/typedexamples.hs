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

failure :: Comp
failure = OpA "fail" Vunit (DotA "y" Any (absurd (Var "y" 0)))

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

-- | @runIncT@ is a macro to help apply the initial value
runIncT :: Int -> Comp -> ValueType -> Comp
runIncT s c vt = DoA "c'" (HandleA (UFunction (UFirst UNone)) hIncT c) (Tfunction Tint vt) $ App (Var "c'" 0) (Vint s)

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
tInc1Comp = (HandleA (UList UNone) (hOnceT) (runIncT 0 cIncT (Tpair (Tlist Tint) Tint)))
tInc1 = checkFile tInc1Gam tInc1Sig tInc1Comp (Tlist (Tpair Tint Tint))

tInc2Gam = Map.fromList([
  ("tIncA", Tlist Tint), 
  ("tOnceA", Tint)])
tInc2Comp = runIncT 0 (HandleA (UList UNone) (hOnceT) (cIncT)) (Tpair (Tlist Tint) Tint)
tInc2 = checkFile tInc2Gam tInc1Sig tInc2Comp (Tpair (Tlist Tint) Tint)

tInc3Sig = Map.fromList([
  ("inc", Lop "inc" Tunit Tunit), 
  ("choose", Lop "choose" Tunit Tbool),
  ("once", Lsc "once" Tunit Tint)])
tInc3Comp = HandleA (UList UNone) (hOnceT) (runIncT 0 cFwdT (Tpair (Tlist Tint) Tint))
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


tCatchGam1 = Map.fromList([
  ("tCatchA", Tint),
  ("tIncA", Tint)])
tCatchSig1 = Map.fromList([
  ("raise", Lop "raise" Tstr Any),
  ("catch", Lsc "catch" Tstr Tint),
  ("inc", Lop "inc" Tunit Tint)])
tCatchComp1 = HandleA (USum UNone UNone) hExceptT (runIncT 42 cCatchT (Tsum Tstr (Tpair Tint Tint)))
tCatch1 = checkFile tCatchGam1 tCatchSig1 tCatchComp1 (Tsum Tstr (Tpair Tint Tint))

tCatchComp2 = runIncT 42 (HandleA (USum UNone UNone) hExceptT cCatchT) (Tpair (Tsum Tstr Tint) Tint)
tCatch2 = checkFile tCatchGam1 tCatchSig1 tCatchComp2 (Tpair (Tsum Tstr Tint) Tint)

cIncrT :: Comp
cIncrT = DoA "x" (op "inc" Vunit Tint) Tint $
       DoA "b" (Binop Larger (Var "x" 0) (Vint 10)) Tbool $
       If (Var "b" 0) (op "raise" (Vstr "Overflow") Tint) (Return (Var "x" 1))


cExT :: Comp
cExT = DoA "_" cIncrT Any $
      DoA "_" cIncrT Any $
      DoA "_" cIncrT Any $
      Return (Vstr "success")

tCatchSig2 = Map.fromList([
  ("raise", Lop "raise" Tstr Any),
  ("catch", Lsc "catch" Tstr Tstr),
  ("inc", Lop "inc" Tunit Tint)])

cCatch2T :: Comp
cCatch2T = DoA "_" (cIncrT) Any $
      sc "catch" (Vstr "Overflow") "b" Tbool (If (Var "b" 0) cExT (Return (Vstr "fail"))) Tstr

tCatchComp3 = HandleA (USum UNone UNone) hExceptT (runIncT 1 cCatch2T (Tsum Tstr (Tpair Tstr Tint)))
tCatch3 = checkFile tCatchGam1 tCatchSig2 tCatchComp3 (Tsum Tstr (Tpair Tstr Tint))


tCatchComp4 = runIncT 1 (HandleA (USum UNone UNone) hExceptT cCatch2T) (Tpair (Tsum Tstr Tstr) Tint)
tCatch4 = checkFile tCatchGam1 tCatchSig2 tCatchComp4 (Tpair (Tsum Tstr Tstr) Tint)

tCatchComp5 = HandleA (USum UNone UNone) hExceptT (runIncT 8 cCatch2T (Tsum Tstr (Tpair Tstr Tint)))
tCatch5 = checkFile tCatchGam1 tCatchSig2 tCatchComp5 (Tsum Tstr (Tpair Tstr Tint))

tCatchComp6 = runIncT 8 (HandleA (USum UNone UNone) hExceptT cCatch2T) (Tpair (Tsum Tstr Tstr) Tint)
tCatch6 = checkFile tCatchGam1 tCatchSig2 tCatchComp6 (Tpair (Tsum Tstr Tstr) Tint)

tCatchComp7 = HandleA (USum UNone UNone) hExceptT (runIncT 42 cCatch2T (Tsum Tstr (Tpair Tstr Tint)))
tCatch7 = checkFile tCatchGam1 tCatchSig2 tCatchComp7 (Tsum Tstr (Tpair Tstr Tint))

tCatchComp8 = runIncT 42 (HandleA (USum UNone UNone) hExceptT cCatch2T) (Tpair (Tsum Tstr Tstr) Tint)
tCatch8 = checkFile tCatchGam1 tCatchSig2 tCatchComp8 (Tpair (Tsum Tstr Tstr) Tint)


----------------------------------------------

hStateT :: Handler
hStateT = Handler
  "hState" ["get", "put"] ["local"] []
  ("x", Return . LamA "m" Tmem $ Return (Vpair (Var "x" 1, Var "m" 0)))
  (\ oplabel -> case oplabel of
    "get" -> Just ("x", "k",
      Return . LamA "m" Tmem $ DoA "v" (Binop Retrieve (Var "x" 2) (Var "m" 0)) Any $
                         DoA "k'" (App (Var "k" 2) (Var "v" 0)) (Tfunction Tmem (Tpair Any Tmem)) $
                         App (Var "k'" 0) (Var "m" 2))
    "put" -> Just ("pa", "k",
      Return . LamA "m" Tmem $ DoA "k'" (App (Var "k" 1) Vunit) Any $
                         DoA "m'" (Binop Update (Var "pa" 3) (Var "m" 1)) Tmem $
                         App (Var "k'" 1) (Var "m'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "local" -> Just ("xv", "p", "k",
      Return . LamA "m" Tmem $ DoA "x" (Unop Fst (Var "xv" 3)) Any $
                         DoA "v" (Unop Snd (Var "xv" 4)) Any $
                         DoA "um" (Binop Update (Var "xv" 5) (Var "m" 2)) Tmem $
                         DoA "p'" (App (Var "p" 5) Vunit) Any $
                         DoA "tm" (App (Var "p'" 0) (Var "um" 1)) Any $
                         DoA "t" (Unop Fst (Var "tm" 0)) Any$
                         DoA "m'" (Unop Snd (Var "tm" 1)) Tmem $
                         DoA "k'" (App (Var "k" 8) (Var "t" 1)) (Tfunction Tmem (Any))$
                         DoA "oldv" (Binop Retrieve (Var "x" 7) (Var "m" 8)) (TValVar "hStateA") $
                         DoA "newm" (Binop Update (Vpair (Var "x" 8, Var "oldv" 0)) (Var "m'" 2)) Tmem $
                         App (Var "k'" 2) (Var "newm" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "m" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" (Any) $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any)$
                App (Var "p'" 0) (Var "m" 2)
    , LamA "zs" (Tpair (Any) (Tint)) $ DoA "z" (Unop Fst (Var "zs" 0)) Any $
                 DoA "s'" (Unop Snd (Var "zs" 1)) Tint $
                 DoA "k'" (App (Var "k" 4) (Var "z" 1)) (Tfunction Tint Any) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- | @cState@ refers to the @c_state@ program in Section 7.4
cStateT :: Comp
cStateT = DoA "_" (op "put" (Vpair (Vstr "x", Vint 10)) Any) Any $
         DoA "x1" (sc "local" (Vpair (Vstr "x", Vint 42)) "_" Any (op "get" (Vstr "x") Tint) Tint) Tint $
         DoA "x2" (op "get" (Vstr "x") Tint) Tint $
         Return (Vpair (Var "x1" 1, Var "x2" 0))


tStateGam = Map.fromList [("hStateA", Tint)]
tStateSig = Map.fromList [("get", Lop "get" Tstr (Tfunction Tmem (Tpair Tstr Tmem))),
                          ("put", Lop "put" (Tpair Tstr Tint) (Tfunction Tmem (Tpair Tunit Tmem))),
                          ("local", Lsc "local" (Tpair Tstr Tint) Tint)]

-- Handling @cState@:
handle_cStateT :: Comp
handle_cStateT = DoA "m" (Unop Newmem Vunit) Tmem $ 
                DoA "c" (HandleA (UFunction (UFirst UNone)) hStateT cStateT) (Tfunction Tmem (Tpair (Tpair Tint Tint) Tmem))$
                DoA "x" (App (Var "c" 0) (Var "m" 1)) (Tpair (Tpair Tint Tint) Tmem) $
                Unop Fst (Var "x" 0)

tState = checkFile tStateGam tStateSig handle_cStateT (Tpair Tint Tint)

----------------------------------------------

hDepthT :: Handler
hDepthT = Handler
  "hDepth" ["choose", "fail"] ["depth"] []
  ("x", Return . LamA "d" Tint $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . LamA "d" Tint $
      DoA "b" (Binop Eq (Var "d" 0) (Vint 0)) Tbool $
      If (Var "b" 0) (Return (Vlist []))
                     (DoA "k1" (App (Var "k" 2) (Vbool True)) (Tfunction Tint Any)$
                      DoA "k2" (App (Var "k" 3) (Vbool False)) (Tfunction Tint Any)$
                      DoA "d'" (Binop Add (Var "d" 3) (Vint (-1))) Tint $
                      DoA "xs" (App (Var "k1" 2) (Var "d'" 0)) Any $
                      DoA "ys" (App (Var "k2" 2) (Var "d'" 1)) Any $
                      Binop Append (Var "xs" 1) (Var "ys" 0) ))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . LamA "d" Tint $
      DoA "p'" (App (Var "p" 2) Vunit) Any $
      DoA "xs" (App (Var "p'" 0) (Var "d'" 4)) Any $
      Binop ConcatMap (Var "xs" 0) (LamA "v_" (Tpair Any Any) $ DoA "v" (Unop Fst (Var "v_" 0)) Any $
                                         DoA "k'" (App (Var "k" 5) (Var "v" 0)) (Tfunction Tint Any)$
                                         App (Var "k'" 0) (Var "d" 5)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "d" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any) $
                App (Var "p'" 0) (Var "d" 2)
    , LamA "vs" Any $ Binop ConcatMap (Var "vs" 0) (LamA "vd" (Tpair Any Tint) $
        DoA "v" (Unop Fst (Var "vd" 0)) Any $
        DoA "d" (Unop Snd (Var "vd" 1)) Tint $
        DoA "k'" (App (Var "k" 5) (Var "v" 1)) (Tfunction Tint Any) $
        App (Var "k'" 0) (Var "d" 1))
    )))

-- | @hDepth2@ is another handler for @depth@.
-- The depth consumed by the scoped computation is also counted in the global depth bound.
hDepth2T :: Handler
hDepth2T = Handler
  "hDepth" ["choose", "fail"] ["depth"] []
  ("x", Return . LamA "d" Tint $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . LamA "d" Tint $
      DoA "b" (Binop Eq (Var "d" 0) (Vint 0)) Tbool $
      If (Var "b" 0) (Return (Vlist []))
                     (DoA "k1" (App (Var "k" 2) (Vbool True)) (Tfunction Tint Any) $
                      DoA "k2" (App (Var "k" 3) (Vbool False)) (Tfunction Tint Any)$
                      DoA "d'" (Binop Add (Var "d" 3) (Vint (-1))) Tint $
                      DoA "xs" (App (Var "k1" 2) (Var "d'" 0)) Any $
                      DoA "ys" (App (Var "k2" 2) (Var "d'" 1)) Any $
                      Binop Append (Var "xs" 1) (Var "ys" 0) ))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . LamA "d" Tint $
      DoA "p'" (App (Var "p" 2) Vunit) Any $
      DoA "md" (Binop Min (Var "d'" 4) (Var "d" 1)) Tint $
      DoA "xs" (App (Var "p'" 1) (Var "md" 0)) (Tlist Any) $
      Binop ConcatMap (Var "xs" 0) (LamA "vd" (Tpair Any Tint) $ DoA "v" (Unop Fst (Var "vd" 0)) Any $
                                         DoA "rd" (Unop Snd (Var "vd" 1)) Tint $
                                         DoA "consumed" (Binop Minus (Var "md" 4) (Var "rd" 0)) Tint $
                                         DoA "trued" (Binop Minus (Var "d" 7) (Var "consumed" 0)) Tint $
                                         DoA "k'" (App (Var "k" 9) (Var "v" 3)) (Tfunction Tint Any)$
                                         App (Var "k'" 0) (Var "trued" 1)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "d" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any) $
                App (Var "p'" 0) (Var "d" 2)
    , LamA "vs" (Any) $ Binop ConcatMap (Var "vs" 0) (LamA "vd" (Tpair Any Tint) $
        DoA "v" (Unop Fst (Var "vd" 0)) Any $
        DoA "d" (Unop Snd (Var "vd" 1)) Tint $
        DoA "k'" (App (Var "k" 5) (Var "v" 1)) (Tfunction Tint Any) $
        App (Var "k'" 0) (Var "d" 1))
    )))


cDepthT :: Comp
cDepthT = ScA "depth" (Vint 1) (DotA "_" Any
 (DoA "b" (op "choose" Vunit Tbool) Tbool $
 If (Var "b" 0) (Return (Vint 1))
                ( DoA "b'" (op "choose" Vunit Tbool) Tbool $
                  If (Var "b'" 0)
                     (Return (Vint 2))
                     (Return (Vint 3)))))
  (DotA "x" Tint (DoA "b" (op "choose" Vunit Tbool) Tbool $
   If (Var "b" 0) (Return (Var "x" 1))
                  ( DoA "b'" (op "choose" Vunit Tbool) Tbool $
                    If (Var "b'" 0)
                       (Return (Vint 4))
                       (DoA "b''" (op "choose" Vunit Tbool) Tbool $
                         If (Var "b''" 0)
                            (Return (Vint 5))
                            (Return (Vint 6))))))

tDepthGam = Map.empty
tDepthSig = Map.fromList([
  ("depth", Lsc "depth" Tint Tint),
  ("choose", Lop "choose" Tunit Tbool),
  ("fail", Lop "fail" Any Any)
  ])

tDepthComp1 = DoA "f" (HandleA (UFunction (UList (UFirst UNone))) hDepthT cDepthT) (Tfunction Tint (Tlist (Tpair Tint Tint))) $ App (Var "f" 0) (Vint 2)
tDepth1 = checkFile tDepthGam tDepthSig tDepthComp1 (Tlist (Tpair Tint Tint))

tDepthComp2 = DoA "f" (HandleA (UFunction (UList (UFirst UNone))) hDepth2T cDepthT) (Tfunction Tint (Tlist (Tpair Tint Tint))) $ App (Var "f" 0) (Vint 2)
tDepth2 = checkFile tDepthGam tDepthSig tDepthComp2 (Tlist (Tpair Tint Tint))

--------------------------------------------------------------------------------
-- TODO
-- hTokenT :: Handler
-- hTokenT = Handler
--   "hToken" ["token"] [] []
--   ("x", Return . LamA "s" Tstr $ Return (Vpair (Var "x" 1, Var "s" 0)))
--   (\ oplabel -> case oplabel of
--     "token" -> Just ("x", "k", Return . LamA "s" Tstr $
--       DoA "b" (Binop Eq (Var "s" 0) (Vstr "")) Tbool $
--       If (Var "b" 0) failure
--                      ( DoA "x'" (Unop HeadS (Var "s" 1)) Tstr $
--                        DoA "xs" (Unop TailS (Var "s" 2)) Tstr $
--                        DoA "b" (Binop Eq (Var "x" 5) (Var "x'" 1)) Tbool $
--                        If (Var "b" 0) (app2 (Var "k" 5) (Var "x" 6) (Var "xs" 1)) failure))
--     _ -> Nothing)
--   (\ sclabel -> case sclabel of
--     _ -> Nothing)
--   (\ forlabel -> case forlabel of
--     _ -> Nothing)
--   ("f", "p", "k", Return . LamA "s" Tstr $ App (Var "f" 3) (Vpair
--     ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tstr Any) $
--                 App (Var "p'" 0) (Var "s" 2)
--     , LamA "zs" (Tpair Any Tstr) $ DoA "z" (Unop Fst (Var "zs" 0)) Any $
--                  DoA "s'" (Unop Snd (Var "zs" 1)) Tstr $
--                  DoA "k'" (App (Var "k" 4) (Var "z" 1)) Any $
--                  App (Var "k'" 0) (Var "s'" 1)
--     )))

-- -- | @<>@ refers to the syntactic sugar @<>@ in Section 7.6
-- (<>) :: Comp -> Comp -> Comp
-- x <> y = OpA "choose" Vunit (DotA "b" Tbool (If (Var "b" 0) (shiftC 1 x) (shiftC 1 y)))

-- -- Parsers defined in Fig. 7 :
-- digit :: Value
-- digit =  LamA "_" Any $ 
--          op "token" (Vchar '0') Any
--       <> op "token" (Vchar '1') Any
--       <> op "token" (Vchar '2') Any
--       <> op "token" (Vchar '3') Any
--       <> op "token" (Vchar '4') Any
--       <> op "token" (Vchar '5') Any
--       <> op "token" (Vchar '6') Any
--       <> op "token" (Vchar '7') Any
--       <> op "token" (Vchar '8') Any
--       <> op "token" (Vchar '9') Any
-- -- | For simplicity, we directly use Haskell's recursion to implement the recursive function @many1@.
-- many1 :: Value -> Comp
-- many1 p = DoA "a" (App p Vunit) Any $
--           DoA "as" (many1 p <> Return (Vstr "")) Any $
--           DoA "x" (Binop ConsS (Var "a" 1) (Var "as" 0)) Any $
--           Return (Var "x" 0)
-- expr :: Value
-- expr = LamA "_" Any $
--        (DoA "i" (App term Vunit) Any $
--         DoA "_" (op "token" (Vchar '+') Any) Any $
--         DoA "j" (App expr Vunit) Any $
--         DoA "x" (Binop Add (Var "i" 2) (Var "j" 0)) Any $
--         Return (Var "x" 0))
--     <> (DoA "i" (App term Vunit) Any $ Return (Var "i" 0))
-- term :: Value
-- term = LamA "_" Any $
--        (DoA "i" (App factor Vunit) Any $
--         DoA "_" (op "token" (Vchar '*') Any) Any $
--         DoA "j" (App term Vunit) Any $
--         DoA "x" (Binop Mul (Var "i" 2) (Var "j" 0)) Any $
--         Return (Var "x" 0))
--     <> (DoA "i" (App factor Vunit) Any $ Return (Var "i" 0))
-- factor :: Value
-- factor = LamA "_" Any $
--          (DoA "ds" (many1 digit) Any $
--           DoA "x" (Unop Read (Var "ds" 0)) Any $
--           Return (Var "x" 0))
--       <> (DoA "_" (op "token" (Vchar '(') Any) Any $
--           DoA "i" (App expr Vunit) Any $
--           DoA "_" (op "token" (Vchar ')') Any) Any $
--           Return (Var "i" 1))

-- -- | @expr1@ refers to the @expr_1@ parser in Section 7.6
-- expr1 :: Value
-- expr1 = LamA "_" Any $
--         DoA "i" (App term Vunit) Tint $
--         sc "call" Vunit "_" Any  (DoA "_" (op "token" (Vchar '+') Any) Any $
--                                   DoA "_" (op "cut" Vunit Any) Any $
--                                   DoA "j" (App expr1 Vunit) Tint $
--                                   DoA "x" (Binop Add (Var "i" 4) (Var "j" 0)) Tint $
--                                   Return (Var "x" 0) <> Return (Var "i" 1)) Any


-- -- Handling @expr1@:
-- handle_expr1T :: Comp
-- handle_expr1T = hCutT # (DoA "c" (hTokenT # App expr1 Vunit) (Tfunction Tstr Any) $
--                        App (Var "c" 0) (Vstr "(2+5)*8"))

-- -- Handling @expr@:
-- handle_exprT :: Comp
-- handle_exprT = hCutT # (DoA "c" (hTokenT # App expr Vunit) (Tfunction Tstr Any) $
--                       App (Var "c" 0) (Vstr "(2+5)*8"))

-- tParseGam = Map.empty
-- tParseSig = Map.fromList([
--   ("token", Lop "token" (Tpair Tstr Any) (Tfunction Tstr Any)),
--   ("cut", Lop "cut" Tunit (Tfunction Tunit Any)),
--   ("call", Lop "call" Tunit (Tfunction Tunit Any))
--   ])
-- tParse1 = checkFile tParseGam tParseSig handle_expr1T (Tret (Tlist (Tpair Tint Tstr)))

------------------------------------------------------------------------

-- TODO
-- hReaderT :: Handler
-- hReaderT = Handler
--   "hReader" ["ask"] ["local"] []
--   ("x", Return . LamA "m" Tmem $ Return (Vpair (Var "x" 1, Var "m" 0)))
--   (\ oplabel -> case oplabel of
--     "ask" -> Just ("_", "k",
--       Return . LamA "m" Tmem $ DoA "env" (Binop Retrieve (Vstr "readerEnv") (Var "m" 0)) Any $
--                          DoA "k'" (App (Var "k" 2) (Var "env" 0)) (Tfunction Tmem Any) $
--                          App (Var "k'" 0) (Var "m" 2))
--     _ -> Nothing)
--   (\ sclabel -> case sclabel of
--     "local" -> Just ("x", "p", "k",
--       Return . LamA "m" Tmem $ DoA "envKey" (Return (Vstr "readerEnv")) Tstr $
--                          DoA "oldEnv" (Binop Retrieve (Var "envKey" 0) (Var "m" 1)) Any $
--                          DoA "newEnv" (App (Var "x" 5) (Var "oldEnv" 0)) Any $ 
--                          DoA "um" (Binop Update (Vpair ((Var "envKey" 2), (Var "newEnv" 0))) (Var "m" 3)) Tmem $
--                          DoA "p'" (App (Var "p" 6) Vunit) Any $
--                          DoA "tm" (App (Var "p'" 0) (Var "um" 1)) (Tpair Any Any) $
--                          DoA "t" (Unop Fst (Var "tm" 0)) Any $
--                          DoA "m'" (Unop Snd (Var "tm" 1)) Tmem $
--                          DoA "k'" (App (Var "k" 9) (Var "t" 1)) Any $
--                          DoA "newm" (Binop Update (Vpair ((Var "envKey" 8), (Var "oldEnv" 7))) (Var "m'" 1)) Tmem $
--                          App (Var "k'" 1) (Var "newm" 0))
--     _ -> Nothing)
--   (\ forlabel -> case forlabel of
--     _ -> Nothing)
--   ("f", "p", "k", Return . LamA "m" Tmem $
--         DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
--         App (Var "f" 4) (Var "pk" 0)
--   )

-- cReaderT :: Comp
-- cReaderT = DoA "x1" (op "ask" Vunit Any) Any $
--           DoA "x2" ((sc "local" (Lam "x" (Binop Append (Var "x" 0) (Vlist [Vint 5])))) "_" Any (op "ask" Vunit Any) Any) Any $
--           DoA "x3" (op "ask" Vunit Any) Any $ 
--           Return (Vpair ((Vpair (Var "x1" 0, Var "x3" 1)), (Var "x3" 2)))

-- runReaderT :: Value -> Comp -> Comp
-- runReaderT s c = sc "local" s "_" Any c Any

-- handle_cReaderT :: Value -> Comp
-- handle_cReaderT c = DoA "m" (Unop Newmem (Vunit)) Tmem $
--                    DoA "c" (HandleA (UFunction (UFirst UNone)) hReaderT (runReaderT (c) cReaderT)) (Tfunction Tmem Any) $
--                    DoA "x" (App (Var "c" 0) (Var "m" 1)) (Tlist Any) $
--                    Unop Fst (Var "x" 0)

-- -- @cReader@ example:
-- example_cReaderT :: Comp
-- example_cReaderT = handle_cReaderT (LamA "x" Any (Return (Vlist [(Vint 1), (Vint 2), (Vint 3), (Vint 4)])))


-- tReaderGam = Map.empty
-- tReaderSig = Map.fromList([
--   ("ask", Lop "ask" Tunit (Tfunction Tmem Any)),
--   ("local", Lop "local" (Tfunction Tmem Any) (Tfunction Tmem Any))
--   ])

-- tReader = checkFile tReaderGam tReaderSig example_cReaderT (Tret (Tpair (Tpair (Tlist Tint) (Tlist Tint)) (Tlist Tint)))

hAccumT :: Handler
hAccumT = Handler
  "hAccum" ["accum"] [] ["for"]
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair Tint (Tlist Tunit)) $
      DoA "m'" (Unop Fst (Var "k'" 0)) Tint $
      DoA "s" (Unop Snd (Var "k'" 1)) (Tlist Tunit) $
      DoA "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) Tint $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" ->      (Just ("list", "l", "k", 
          DoA "pairs" (App (Var "l" 1) (Var "list" 2)) (Tlist (Tpair Tint Tunit)) $
          DoA "first" (Binop Map (Var "pairs" 0) (LamA "l'" (Tlist (Tpair Tint Tunit)) (Unop Fst (Var "l'" 0)))) (Tlist Tint) $
          DoA "second" (Binop Map (Var "pairs" 1) (LamA "l'" (Tlist (Tpair Tint Tunit)) (Unop Snd (Var "l'" 0)))) (Tlist Tunit) $
          DoA "k'" (App (Var "k" 3) (Var "second" 0)) (Tpair Tint (Tlist Tunit)) $
          LetrecA "reduce" (Tfunction (Tlist Tint) Tint) (LamA "l" (Tlist Tint) . DoA "n" (Unop Empty (Var "l" 0)) Tbool $
                                    If (Var "n" 0) (Return (Vint 0)) (DoA "h" (Unop Head (Var "l" 1)) Tint $
                                                                      DoA "t" (Unop Tail (Var "l" 2)) (Tlist Tint)$
                                                                      DoA "y" (App (Var "reduce" 4) (Var "t" 0)) Tint $
                                                                      DoA "x" (Binop Add (Var "h" 2) (Var "y" 0)) Tint $
                                                                      Return (Var "x" 0))) 
            (DoA "rest" (App (Var "reduce" 0) (Var "first" 3)) Tint $
            DoA "base" (Unop Fst (Var "k'" 2)) Tint $
            DoA "k''" (Unop Snd (Var "k'" 3)) (Tlist Tunit) $
            DoA "res" (Binop Add (Var "base" 1) (Var "rest" 2)) Tint $
            Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

hPureT :: Handler
hPureT = Parallel
  (("list", "p", "k", 
      DoA "result" (Binop Map (Var "list" 2) (Var "p" 1)) (Tlist Any) $
      App (Var "k" 1) (Var "result" 0)))
  (("x", Return (Var "x" 0)))
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

cAccumT :: Comp
cAccumT = ForA "for" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5]) (DotA "y" Tint (op "accum" (Var "y" 0) Any)) (DotA "z" Any (Return (Var "z" 0)))


hAccumNoForT :: Handler
hAccumNoForT = Handler
  "hAccum" ["accum"] [] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair Tint (Tlist (Tpair Tint Tunit))) $
      DoA "m'" (Unop Fst (Var "k'" 0)) Tint $
      DoA "s" (Unop Snd (Var "k'" 1)) (Tlist (Tpair Tint Tunit)) $
      DoA "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) Tint $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )


tAccumGam = Map.empty
tAccumSig = Map.fromList([
  ("accum", Lop "accum" Tint (Tpair Tint Any)),
  ("for", Lfor "for" Any)
  ])
tAccumComp1 = HandleA UNone hPureT (HandleA  (USecond UNone) hAccumT cAccumT)
tAccum1 = checkFile tAccumGam tAccumSig tAccumComp1 (Tpair Tint (Tlist Tunit))

tAccumComp2 = HandleA UNone hPureT (HandleA (USecond UNone) hAccumNoForT cAccumT)
tAccum2 = checkFile tAccumGam tAccumSig tAccumComp2 (Tpair Tint (Tlist (Tpair Tint Tunit)))

tAccumSigSc = Map.fromList([
  ("accum", Lop "accum" Tint (Tpair Tint Any)),
  ("for", Lsc "for" Any Any)
  ])
tAccumComp3 = HandleA UNone hPureScT (HandleA (USecond UNone) hAccumSc1T cAccumScT)
tAccum3 = checkFile tAccumGam tAccumSigSc tAccumComp3 (Tpair Tint (Tlist Tunit))

tAccumComp4 = HandleA UNone hPureScT (HandleA (USecond UNone) hAccumScNoForT cAccumScT)
tAccum4 = checkFile tAccumGam tAccumSigSc tAccumComp4 (Tpair Tint (Tlist (Tpair Tint Tunit)))


hAccumSc1T :: Handler
hAccumSc1T = Handler
  "hAccumSc" ["accum"] ["for"] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair Tint (Tlist (Tpair Tint Tunit))) $
      DoA "m'" (Unop Fst (Var "k'" 0)) Tint $
      DoA "s" (Unop Snd (Var "k'" 1)) (Tlist (Tpair Tint Tunit)) $
      DoA "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) Tint $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" ->      (Just ("list", "l", "k", 
          DoA "pairs" (ScA "for" (Var "x" 2) (DotA "y" Tint (App (Var "p" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))) (Tlist (Tpair Tint Tunit)) $
          DoA "first" (Binop Map (Var "pairs" 0) (LamA "l'" (Tlist (Tpair Tint Tunit)) (Unop Fst (Var "l'" 0)))) (Tlist Tint) $
          DoA "second" (Binop Map (Var "pairs" 1) (LamA "l'" (Tlist (Tpair Tint Tunit)) (Unop Snd (Var "l'" 0)))) (Tlist Tunit) $
          DoA "k'" (App (Var "k" 3) (Var "second" 0)) (Tpair Tint (Tlist Tunit)) $
          LetrecA "reduce" (Tfunction (Tlist Tint) Tint) (LamA "l" (Tlist Tint) . DoA "n" (Unop Empty (Var "l" 0)) Tbool $
                                    If (Var "n" 0) (Return (Vint 0)) (DoA "h" (Unop Head (Var "l" 1)) Tint $
                                                                      DoA "t" (Unop Tail (Var "l" 2)) (Tlist Tint)$
                                                                      DoA "y" (App (Var "reduce" 4) (Var "t" 0)) Tint $
                                                                      DoA "x" (Binop Add (Var "h" 2) (Var "y" 0)) Tint $
                                                                      Return (Var "x" 0))) 
            (DoA "rest" (App (Var "reduce" 0) (Var "first" 3)) Tint $
            DoA "base" (Unop Fst (Var "k'" 2)) Tint $
            DoA "k''" (Unop Snd (Var "k'" 3)) (Tlist Tunit) $
            DoA "res" (Binop Add (Var "base" 1) (Var "rest" 2)) Tint $
            Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

hPureScT :: Handler
hPureScT = Handler
  "hPureSc" [] ["for"] []
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              DoA "results" (Binop Map (Var "x" 2) (Var "p" 1)) Any $
              App (Var "k" 1) (Var "results" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

cAccumScT :: Comp
cAccumScT = ScA "for" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5]) (DotA "y" Tint (op "accum" (Var "y" 0) Any)) (DotA "z" Any (Return (Var "z" 0)))

hAccumScNoForT :: Handler
hAccumScNoForT = Handler
  "hAccumSc" ["accum"] [] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair Tint (Tlist (Tpair Tint Tunit))) $
      DoA "m'" (Unop Fst (Var "k'" 0)) Tint $
      DoA "s" (Unop Snd (Var "k'" 1)) (Tlist (Tpair Tint Tunit)) $
      DoA "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) Tint $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )


hAccumST :: Handler
hAccumST = Handler
  "hAccum" ["accum"] [] ["for"]
  ("x", Return (Vpair (Vstr "", Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair Tstr (Tsum Tstr Tunit))$
      DoA "m'" (Unop Fst (Var "k'" 0)) Tstr $
      DoA "s" (Unop Snd (Var "k'" 1)) (Tsum Tstr Tunit) $
      DoA "m''" (Binop AppendS (Var "x" 4) (Var "m'" 1)) Tstr $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" -> (Just ("list", "l", "k", 
          DoA "pairs" (App (Var "l" 1) (Var "list" 2)) (Tlist (Tpair Tstr (Tsum Tstr Tunit))) $
          DoA "first" (Binop Map (Var "pairs" 0) (LamA "l" (Tlist (Tpair Tstr (Tsum Tstr Tunit))) (Unop Fst (Var "l" 0)))) (Tlist Tstr) $
          DoA "second" (Binop Map (Var "pairs" 1) (LamA "l" (Tlist (Tpair Tstr (Tsum Tstr Tunit))) (Unop Snd (Var "l" 0)))) (Tlist (Tsum Tstr Tunit)) $
          DoA "k'" (App (Var "k" 3) (Var "second" 0)) (Tpair Tstr (Tsum Tstr Tunit)) $
          LetrecA "reduce" (Tfunction (Tlist Tstr) Tstr) (LamA "l" (Tlist Tstr) . DoA "n" (Unop Empty (Var "l" 0)) Tbool $
                                If (Var "n" 0) (Return (Vstr "")) (DoA "h" (Unop Head (Var "l" 1)) Tstr $
                                                                  DoA "t" (Unop Tail (Var "l" 2)) (Tlist Tstr) $
                                                                  DoA "y" (App (Var "reduce" 4) (Var "t" 0)) Tstr $
                                                                  DoA "x" (Binop AppendS (Var "h" 2) (Var "y" 0)) Tstr $
                                                                  Return (Var "x" 0))) 
            (DoA "rest" (App (Var "reduce" 0) (Var "first" 3)) Tstr $
            DoA "base" (Unop Fst (Var "k'" 2)) Tstr $
            DoA "k''" (Unop Snd (Var "k'" 3)) (Tsum Tstr Tunit) $
            DoA "res" (Binop AppendS (Var "base" 1) (Var "rest" 2)) Tstr $
            Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))
    _ -> Nothing)
  ("f", "p", "k", 
      DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
      App (Var "f" 3) (Var "pk" 0)
  )


hWeakT :: Handler
hWeakT = Handler
  "hWeak" ["throw"] [] ["for"]
  ("x", Return (Vsum (Right (Var "x" 0))))
  (\ oplabel -> case oplabel of
    "throw" -> Just ("x", "k", Return (Vsum (Left (Var "x" 1))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" -> (Just ("list", "l", "k",
          DoA "results" (App (Var "l" 1) (Var "list" 2)) Any $ 
          DoA "FirstFail" (Unop FirstFail (Var "results" 0)) (Tsum Tstr Tunit) $
          Case (Var "FirstFail" 0) 
            "error" (Return $ Vsum $ Left (Var "error" 0))
            "t" (App (Var "k" 3) (Var "t" 0))
        ))
    _ -> Nothing)
  ("f", "p", "k", 
      DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
      App (Var "f" 3) (Var "pk" 0)
  )


cWeakT :: Comp
cWeakT = DoA "_" (OpA "accum" (Vstr "start ") (DotA "y" Any (Return (Var "y" 0)))) Any $ 
         (ForA "for" (Vlist [Vstr "1", Vstr "2", Vstr "3", Vstr "4", Vstr "5"])
         (DotA "y" Tstr (Do "eq2" (Binop Eq (Var "y" 0) (Vstr "2")) $
         If (Var "eq2" 0)   (DoA "_" (OpA "accum" (Vstr "!") (DotA "y" Any (Return (Var "y" 0)))) Any $
                            DoA "_" (OpA "throw" (Vstr "error") (DotA "y" Any (Return (Var "y" 0)))) Any $
                            OpA "accum" (Vstr "unreachable") (DotA "y" Any (Return (Var "y" 0))))
        (OpA "accum" (Var "y" 1) (DotA "y" Any (Return (Var "y" 0))))))
        (DotA "z" Any (Return (Var "z" 0))))

tWeakGam = Map.empty
tWeakSig = Map.fromList([
  ("accum", Lop "accum" Tstr (Tpair Tstr Any)),
  ("throw", Lop "throw" Tstr (Tpair Tstr Any)),
  ("for", Lfor "for" Any)
  ])
tWeakComp1 = HandleA UNone hPureT (HandleA (USecond UNone) hAccumST (HandleA (USum UNone UNone) hWeakT cWeakT))
tWeak1 = checkFile tWeakGam tWeakSig tWeakComp1 (Tpair Tstr (Tsum Tstr Tunit))


hAccumSScT :: Handler
hAccumSScT = Handler
  "hAccumSc" ["accum"] ["for"] [] 
  ("x", Return (Vpair (Vstr "", Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair Tstr (Tsum Tstr Tunit))$
      DoA "m'" (Unop Fst (Var "k'" 0)) Tstr $
      DoA "s" (Unop Snd (Var "k'" 1)) (Tsum Tstr Tunit) $
      DoA "m''" (Binop AppendS (Var "x" 4) (Var "m'" 1)) Tstr $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              DoA "pairs" (ScA "for" (Var "x" 2) (DotA "y" Any (App (Var "p" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))) (Tlist (Tpair Tstr (Tsum Tstr Tunit)))  $
              DoA "first" (Binop Map (Var "pairs" 0) (LamA "l" (Tlist (Tpair Tstr (Tsum Tstr Tunit))) (Unop Fst (Var "l" 0)))) (Tlist Tstr) $
              DoA "second" (Binop Map (Var "pairs" 1) (LamA "l" (Tlist (Tpair Tstr (Tsum Tstr Tunit))) (Unop Snd (Var "l" 0)))) (Tlist (Tsum Tstr Tunit)) $
              DoA "k'" (App (Var "k" 3) (Var "second" 0)) (Tpair Tstr (Tsum Tstr Tunit)) $
              LetrecA "reduce" (Tfunction (Tlist Tstr) Tstr) (LamA "l" (Tlist Tstr) . DoA "n" (Unop Empty (Var "l" 0)) Tbool $
                                    If (Var "n" 0) (Return (Vstr "")) (DoA "h" (Unop Head (Var "l" 1)) Tstr $
                                                                      DoA "t" (Unop Tail (Var "l" 2)) (Tlist Tstr) $
                                                                      DoA "y" (App (Var "reduce" 4) (Var "t" 0)) Tstr $
                                                                      DoA "x" (Binop AppendS (Var "h" 2) (Var "y" 0)) Tstr $
                                                                      Return (Var "x" 0))) 
                (DoA "rest" (App (Var "reduce" 0) (Var "first" 3)) Tstr $
                DoA "base" (Unop Fst (Var "k'" 2)) Tstr $
                DoA "k''" (Unop Snd (Var "k'" 3)) (Tsum Tstr Tunit) $
                DoA "res" (Binop AppendS (Var "base" 1) (Var "rest" 2)) Tstr $
                Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
      DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
      App (Var "f" 3) (Var "pk" 0)
  )


hWeakScT :: Handler
hWeakScT = Handler
  "hWeak" ["throw"] ["for"] []
  ("x", Return (Vsum (Right (Var "x" 0))))
  (\ oplabel -> case oplabel of
    "throw" -> Just ("x", "k", Return (Vsum (Left (Var "x" 1))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k",
      DoA "results" (ScA "for" (Var "x" 2) (DotA "y" Any (App (Var "p" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))) Any $ 
      DoA "FirstFail" (Unop FirstFail (Var "results" 0)) (Tsum Tstr Tunit) $
      Case (Var "FirstFail" 0) 
        "error" (Return $ Vsum $ Left (Var "error" 0))
        "t" (App (Var "k" 3) (Var "t" 0)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

cWeakScT :: Comp
cWeakScT = DoA "_" (OpA "accum" (Vstr "start ") (DotA "y" Any (Return (Var "y" 0)))) Any $ 
         (ScA "for" (Vlist [Vstr "1", Vstr "2", Vstr "3", Vstr "4", Vstr "5"])
         (DotA "y" Tstr (Do "eq2" (Binop Eq (Var "y" 0) (Vstr "2")) $
         If (Var "eq2" 0)   (DoA "_" (OpA "accum" (Vstr "!") (DotA "y" Any (Return (Var "y" 0)))) Any $
                            DoA "_" (OpA "throw" (Vstr "error") (DotA "y" Any (Return (Var "y" 0)))) Any $
                            OpA "accum" (Vstr "unreachable") (DotA "y" Any (Return (Var "y" 0))))
        (OpA "accum" (Var "y" 1) (DotA "y" Any (Return (Var "y" 0))))))
        (DotA "z" Any (Return (Var "z" 0))))

tWeakSigSc = Map.fromList([
  ("accum", Lop "accum" Tstr (Tpair Tstr Any)),
  ("throw", Lop "throw" Tstr (Tpair Tstr Any)),
  ("for", Lsc "for" Any Any)
  ])

tWeakComp2 = HandleA UNone hPureScT (HandleA (USecond UNone) hAccumSScT (HandleA (USum UNone UNone) hWeakScT cWeakScT))
tWeak2 = checkFile tWeakGam tWeakSigSc tWeakComp2 (Tpair Tstr (Tsum Tstr Tunit))

hPRNGT :: Handler
hPRNGT = Handler
  "hPRNG" ["sampleUniform"] [] ["for"]
  ("x", Return . LamA "key" Tkey $ Return (Var "x" 1))
  (\ oplabel -> case oplabel of
    "sampleUniform" -> Just ("x", "k", Return . LamA "key" Tkey $ 
      DoA "pair" (Unop Rand (Var "key" 0)) (Tpair Tint Tkey) $
      DoA "val" (Unop Fst (Var "pair" 0)) Tint $
      DoA "key" (Unop Snd (Var "pair" 1)) Tkey $
      DoA "cont" (App (Var "k" 4) (Var "val" 1)) (Tfunction Tkey Any) $ 
      App (Var "cont" 0) (Var "key" 1))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    "for" ->   (Just ("list", "l", "k", Return . LamA "key" Tkey $ 
        DoA "keys" (Unop SplitKeyPair (Var "key" 0)) (Tpair Tkey Tkey) $
        DoA "key1" (Unop Fst (Var "keys" 0)) Tkey $
        DoA "key2" (Unop Snd (Var "keys" 1)) Tkey $
        DoA "key1s" (Binop SplitKey (Var "key1" 1) (Var "list" 6)) (Tlist Tkey) $
        DoA "for" (App (Var "l" 6) (Var "list" 7)) (Tlist (Tfunction Tkey Any))$
        DoA "results" (Binop Zip (Var "for" 0) (Var "key1s" 1)) (Tlist Any) $
        DoA "cont" (App (Var "k" 7) (Var "results" 0)) (Tfunction Tkey Any) $
        App (Var "cont" 0) (Var "key2" 4)))
    _ -> Nothing
  )
  ("f", "p", "k", Return . LamA "key" Tkey $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )


cPRNGT :: Comp
cPRNGT = ForA "for" (Vlist [Vunit, Vunit, Vunit]) (DotA "y" Any (OpA "sampleUniform" (Vunit) (DotA "y" (Any) (Return (Var "y" 0))))) (DotA "z" Any (Return (Var "z" 0)))

cPRNGseqT :: Comp
cPRNGseqT = DoA "1" (OpA "sampleUniform" (Vunit) (DotA "y" (Any) (Return (Var "y" 0)))) Tint $
            DoA "2" (OpA "sampleUniform" (Vunit) (DotA "y" (Any) (Return (Var "y" 0)))) Tint $
            DoA "3" (OpA "sampleUniform" (Vunit) (DotA "y" (Any) (Return (Var "y" 0)))) Tint $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

hPureKT :: Handler
hPureKT = Parallel
  (("list", "p", "k", Return . LamA "keys" (Tlist Tkey) $
      DoA "results" (Binop Map (Var "list" 2) (Var "p" 1)) (Tlist (Tfunction Tkey Any))$
      DoA "resultskeys" (Binop Map (Var "results" 0) (Var "keys" 1)) (Tlist Any) $
      App (Var "k" 3) (Var "resultskeys" 0)))
  (("x", Return (Var "x" 0)))
  ("f", "p", "k", Return . LamA "key" Tkey $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )

tPRNGGam = Map.empty
tPRNGSig = Map.fromList([
  ("sampleUniform", Lop "sampleUniform" Tunit (Tfunction Tkey Any)),
  ("for", Lfor "for" Any)
  ])
tPRNGComp1 = HandleA UNone hPureT (DoA "key" (Return (Vkey (mkStdGen 42))) Tkey $ DoA "ex" (HandleA UNone hPureKT (HandleA (UFunction UNone) hPRNGT cPRNGT)) (Tfunction Tkey Any) $ App (Var "ex" 0) (Var "key" 1))
tPRNG1 = checkFile tPRNGGam tPRNGSig tPRNGComp1 (Tlist Tint)

tPRNGComp2 = HandleA UNone hPureT (DoA "key" (Return (Vkey (mkStdGen 42))) Tkey $ DoA "ex" (HandleA UNone hPureT (HandleA (UFunction UNone) hPRNGT cPRNGseqT)) (Tfunction Tkey Any) $ App (Var "ex" 0) (Var "key" 1))
tPRNG2 = checkFile tPRNGGam tPRNGSig tPRNGComp2 (Tlist Tint)

hPRNGScT :: Handler
hPRNGScT = Handler
  "hPRNGSc" ["sampleUniform"] ["for"] []
  ("x", Return . LamA "key" Tkey $ Return (Var "x" 1))
  (\ oplabel -> case oplabel of
    "sampleUniform" -> Just ("x", "k", Return . LamA "key" Tkey $ 
      DoA "pair" (Unop Rand (Var "key" 0)) (Tpair Tint Tkey) $
      DoA "val" (Unop Fst (Var "pair" 0)) Tint $
      DoA "key" (Unop Snd (Var "pair" 1)) Tkey $
      DoA "cont" (App (Var "k" 4) (Var "val" 1)) (Tfunction Tkey Any) $ 
      App (Var "cont" 0) (Var "key" 1))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", Return . LamA "key" Tkey $ 
        DoA "keys" (Unop SplitKeyPair (Var "key" 0)) (Tpair Tkey Tkey) $
        DoA "key1" (Unop Fst (Var "keys" 0)) Tkey $
        DoA "key2" (Unop Snd (Var "keys" 1)) Tkey $
        DoA "key1s" (Binop SplitKey (Var "key1" 1) (Var "list" 6)) (Tlist Tkey) $
        DoA "for" (ScA "for" (Var "x" 7) (DotA "y" Any (App (Var "p" 7) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))) (Tlist (Tfunction Tkey Any))$
        DoA "results" (Binop Zip (Var "for" 0) (Var "key1s" 1)) (Tlist Any) $
        DoA "cont" (App (Var "k" 7) (Var "results" 0)) (Tfunction Tkey Any) $
        App (Var "cont" 0) (Var "key2" 4))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "keys" (Tlist Tkey) $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )

cPRNGScT :: Comp
cPRNGScT = ScA "for" (Vlist [Vunit, Vunit, Vunit]) (DotA "y" Any (OpA "sampleUniform" (Vunit) (DotA "y" Any (Return (Var "y" 0))))) (DotA "z" Any (Return (Var "z" 0)))

cPRNGseqScT :: Comp
cPRNGseqScT =  DoA "1" (OpA "sampleUniform" (Vunit) (DotA "y" Any (Return (Var "y" 0)))) Tint $
            DoA "2" (OpA "sampleUniform" (Vunit) (DotA "y" Any (Return (Var "y" 0)))) Tint $
            DoA "3" (OpA "sampleUniform" (Vunit) (DotA "y" Any (Return (Var "y" 0)))) Tint $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

-- Needs new parallel handler to thread keys through correctly
hPureKScT :: Handler
hPureKScT = Handler
  "hPureSc" [] ["for"] []
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", Return . LamA "keys" (Tlist Tkey) $
                DoA "results" (Binop Map (Var "x" 3) (Var "p" 2)) (Tlist Any) $
                DoA "resultskeys" (Binop Map (Var "results" 0) (Var "keys" 1)) (Tlist Any) $
                App (Var "k" 3) (Var "resultskeys" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "keys" (Tlist Tkey) $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )


tPRNGGamSc = Map.empty
tPRNGSigSc = Map.fromList([
  ("sampleUniform", Lop "sampleUniform" Tunit (Tfunction Tkey Any)),
  ("for", Lsc "for" Any Any)
  ])
tPRNGComp3 = HandleA UNone hPureScT (DoA "key" (Return (Vkey (mkStdGen 42))) Tkey $ DoA "ex" (HandleA UNone hPureKScT (HandleA (UFunction UNone) hPRNGScT cPRNGScT)) (Tfunction Tkey Any) $ App (Var "ex" 0) (Var "key" 1))
tPRNG3 = checkFile tPRNGGamSc tPRNGSigSc tPRNGComp3 (Tlist Tint)

tPRNGComp4 = HandleA UNone hPureT (DoA "key" (Return (Vkey (mkStdGen 42))) Tkey $ DoA "ex" (HandleA UNone hPureScT (HandleA (UFunction UNone) hPRNGScT cPRNGseqScT)) (Tfunction Tkey Any) $ App (Var "ex" 0) (Var "key" 1))
tPRNG4 = checkFile tPRNGGamSc tPRNGSigSc tPRNGComp4 (Tlist Tint)



hAmbT :: Handler
hAmbT = Handler
  "hAmb" ["amb"][] ["for"]
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    "amb" -> Just ("x", "k",
      ForA "for" (Var "x" 1) (DotA "y" (Any) (App (Var "k" 1) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    "for" ->   (Just ("list", "l", "k",
        DoA "results" (App (Var "l" 1) (Var "list" 2)) (Tlist Any) $ 
        DoA "productElts" (Unop CartesianProd (Var "results" 0)) (Tlist Any) $
        ForA "for" (Var "productElts" 0) (DotA "y" Any (App (Var "k" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))
      ))
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )


hAccumLT :: Handler
hAccumLT = Handler
  "hAccumL" ["accum"] [] ["for"]
  ("x", Return (Vpair (Vlist [], Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair (Tlist Any) (Tlist Tunit)) $
      DoA "m'" (Unop Fst (Var "k'" 0)) (Tlist Any) $
      DoA "s" (Unop Snd (Var "k'" 1)) (Tlist Tunit) $
      DoA "m''" (Binop Append (Var "x" 4) (Var "m'" 1)) (Tlist Any) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" ->     (Just ("list", "l", "k", 
          DoA "pairs" (App (Var "l" 1) (Var "list" 2)) (Tlist (Tpair (Tlist Any) (Tlist Tunit))) $
          DoA "first" (Binop Map (Var "pairs" 0) (LamA "l" (Tpair (Tlist Any) (Tlist Tunit)) (Unop Fst (Var "l" 0)))) (Tlist (Tlist Any)) $
          DoA "second" (Binop Map (Var "pairs" 1) (LamA "l" (Tpair (Tlist Any) (Tlist Tunit)) (Unop Snd (Var "l" 0)))) (Tlist (Tlist Tunit)) $
          DoA "k'" (App (Var "k" 3) (Var "second" 0)) (Tpair (Tlist Any) (Nested Tunit)) $
          LetrecA "reduce" (Tfunction (Tlist (Tlist Any)) (Tlist Any)) (LamA "l" (Tlist (Tlist Any)) . DoA "n" (Unop Empty (Var "l" 0)) Tbool $
                                    If (Var "n" 0) (Return (Vlist [])) (DoA "h" (Unop Head (Var "l" 1)) (Tlist Any)$
                                                                      DoA "t" (Unop Tail (Var "l" 2)) (Tlist (Tlist Any)) $
                                                                      DoA "y" (App (Var "reduce" 4) (Var "t" 0)) (Tlist Any) $
                                                                      DoA "x" (Binop Append (Var "h" 2) (Var "y" 0)) (Tlist Any) $
                                                                      Return (Var "x" 0)))
            (DoA "rest" (App (Var "reduce" 0) (Var "first" 3)) (Tlist Any) $
            DoA "base" (Unop Fst (Var "k'" 2)) (Tlist Any) $
            DoA "k''" (Unop Snd (Var "k'" 3)) (Nested Tunit)$
            DoA "res" (Binop Append (Var "base" 1) (Var "rest" 2)) (Tlist Any) $
            Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

cAmbT :: Comp
cAmbT = 
  DoA "d1" (OpA "amb" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5, Vint 6, Vint 7, Vint 8, Vint 9]) (DotA "y" Any (Return (Var "y" 0)))) Tint $
  DoA "d2" (OpA "amb" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5, Vint 6, Vint 7, Vint 8, Vint 9]) (DotA "y" Any (Return (Var "y" 0)))) Tint $
  DoA "res" (Binop Add (Var "d1" 1) (Var "d2" 0)) Tint $
  DoA "eq" (Binop Eq (Var "res" 0) (Vint 13)) Tbool $
  If (Var "eq" 0) (OpA "accum" (Vpair (Var "d1" 3, Var "d2" 2)) (DotA "y" Any (Return Vunit))) (Return Vunit)


tAmbGam = Map.empty
tAmbSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Any) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tint) Tint),
  ("for", Lfor "for" Any)
  ])
tAmbComp = HandleA UNone hPureT (HandleA (USecond UNone) hAccumLT (HandleA (UList (UList UNone)) hAmbT cAmbT))
tAmb = checkFile tAmbGam tAmbSig tAmbComp (Tpair (Tlist (Tpair Tint Tint)) (Tlist (Tlist Tunit)))

cCombT = DoA "d1" (OpA "amb" (Vlist [Vstr "H", Vstr "T"]) (DotA "y" Any (Return (Var "y" 0)))) Tstr $ 
            DoA "d2" (OpA "amb" (Vlist [Vstr "H", Vstr "T"]) (DotA "y" Any (Return (Var "y" 0)))) Tstr $
            DoA "d3" (OpA "amb" (Vlist [Vstr "H", Vstr "T"]) (DotA "y" Any (Return (Var "y" 0)))) Tstr $
            DoA "l1" (Binop AppendS (Var "d1" 2) (Var "d2" 1)) (Tlist Tstr) $
            Binop AppendS (Var "l1" 0) (Var "d3" 1)


tCombSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Any) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tstr) Tstr),
  ("for", Lfor "for" Any)
  ])
tCombComp = HandleA UNone hPureT (HandleA (UList UNone) hAmbT cCombT)
tComb = checkFile tAmbGam tCombSig tCombComp (Tlist (Tlist (Tlist Tstr)))


hAmbScT :: Handler
hAmbScT = Handler
  "hAmbSc" ["amb"] ["for"] []
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    "amb" -> Just ("x", "k",
      ScA "for" (Var "x" 1) (DotA "y" Any (App (Var "k" 1) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              DoA "results" (ScA "for" (Var "x" 2) (DotA "y" Any (App (Var "p" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))) (Tlist Any) $ 
              DoA "productElts" (Unop CartesianProd (Var "results" 0)) (Tlist Any) $
              ScA "for" (Var "productElts" 0) (DotA "y" Any (App (Var "k" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0))))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )


hAccumScLT :: Handler
hAccumScLT = Handler
  "hAccumScL" ["accum"] ["for"] []
  ("x", Return (Vpair (Vlist [], Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair (Tlist Any) (Tlist Tunit)) $
      DoA "m'" (Unop Fst (Var "k'" 0)) (Tlist Any) $
      DoA "s" (Unop Snd (Var "k'" 1)) (Tlist Tunit) $
      DoA "m''" (Binop Append (Var "x" 4) (Var "m'" 1)) (Tlist Any) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k",
              DoA "pairs" (ScA "for" (Var "x" 2) (DotA "y" Any (App (Var "p" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))) (Tlist (Tpair (Tlist Any) (Nested Tunit))) $
              DoA "first" (Binop Map (Var "pairs" 0) (LamA "l" (Tpair (Tlist Any) (Nested Tunit)) (Unop Fst (Var "l" 0)))) (Tlist (Tlist Any)) $
              DoA "second" (Binop Map (Var "pairs" 1) (LamA "l" (Tpair (Tlist Any) (Nested Tunit)) (Unop Snd (Var "l" 0)))) (Nested Tunit) $
              DoA "k'" (App (Var "k" 3) (Var "second" 0)) (Tpair (Tlist Any) (Nested Tunit)) $
              LetrecA "reduce" (Tfunction (Tlist (Tlist Any)) (Tlist Any)) (LamA "l" (Tlist (Tlist Any)) . DoA "n" (Unop Empty (Var "l" 0)) Tbool $
                                        If (Var "n" 0) (Return (Vlist [])) (DoA "h" (Unop Head (Var "l" 1)) (Tlist Any)$
                                                                          DoA "t" (Unop Tail (Var "l" 2)) (Tlist (Tlist Any)) $
                                                                          DoA "y" (App (Var "reduce" 4) (Var "t" 0)) (Tlist Any) $
                                                                          DoA "x" (Binop Append (Var "h" 2) (Var "y" 0)) (Tlist Any) $
                                                                          Return (Var "x" 0)))
                (DoA "rest" (App (Var "reduce" 0) (Var "first" 3)) (Tlist Any) $
                DoA "base" (Unop Fst (Var "k'" 2)) (Tlist Any) $
                DoA "k''" (Unop Snd (Var "k'" 3)) (Nested Tunit)$
                DoA "res" (Binop Append (Var "base" 1) (Var "rest" 2)) (Tlist Any) $
                Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

tAmbScSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Any) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tint) Tint),
  ("for", Lsc "for" Any Any)
  ])

tAmbScComp = HandleA UNone hPureScT (HandleA (USecond UNone) hAccumScLT (HandleA (UList (UList UNone)) hAmbScT cAmbT))
tAmbSc = checkFile tAmbGam tAmbScSig tAmbScComp (Tpair (Nested (Tpair Tint Tint)) (Nested Tunit))

tCombScSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Any) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tstr) Tstr),
  ("for", Lsc "for" Any Any)
  ])

tCombScComp = HandleA UNone hPureScT (HandleA (UList UNone) hAmbScT cCombT)
tCombSc = checkFile tAmbGam tCombScSig tCombScComp (Nested Tstr)


hDepthAmbT :: Handler
hDepthAmbT = Handler
  "hDepthAmb" ["choose", "fail"] ["depth"] []
  ("x", Return . LamA "d" Tint $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . LamA "d" Tint $
      DoA "b" (Binop Eq (Var "d" 0) (Vint 0)) Tbool $
      If (Var "b" 0) (Return (Vlist []))
                     (DoA "b1" (OpA "amb" (Vlist [Vbool True, Vbool False]) (DotA "y" Any (Return (Var "y" 0)))) Tbool $
                      DoA "k1" (App (Var "k" 3) (Var "b1" 0)) (Tfunction Tint Any) $
                      DoA "d'" (Binop Add (Var "d" 3) (Vint (-1))) Tint $
                      App (Var "k1" 1) (Var "d'" 0)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . LamA "d" Tint $
      DoA "p'" (App (Var "p" 2) Vunit) (Tfunction Tint (Tlist Any)) $
      DoA "xs" (App (Var "p'" 0) (Var "d'" 4)) (Tlist Any) $
      Binop ConcatMap (Var "xs" 0) (LamA "v_" (Tpair Any Any) $ DoA "v" (Unop Fst (Var "v_" 0)) Any $
                                         DoA "k'" (App (Var "k" 5) (Var "v" 0)) (Tfunction Tint Any) $
                                         App (Var "k'" 0) (Var "d" 5)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "d" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any) $
                App (Var "p'" 0) (Var "d" 2)
    , LamA "vs" (Tlist Any) $ Binop ConcatMap (Var "vs" 0) (LamA "vd" (Tpair Any Tint) $
        DoA "v" (Unop Fst (Var "vd" 0)) Any $
        DoA "d" (Unop Snd (Var "vd" 1)) Tint $
        DoA "k'" (App (Var "k" 5) (Var "v" 1)) (Tfunction Tint Any) $
        App (Var "k'" 0) (Var "d" 1))
    )))

hDepthAmb2T :: Handler
hDepthAmb2T = Handler
  "hDepthAmb2" ["choose", "fail"] ["depth"] []
  ("x", Return . LamA "d" Tint $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . LamA "d" Tint $
      DoA "b" (Binop Eq (Var "d" 0) (Vint 0)) Tbool $
      If (Var "b" 0) (Return (Vlist []))
                     (DoA "b1" (OpA "amb" (Vlist [Vbool True, Vbool False]) (DotA "y" Any (Return (Var "y" 0)))) Tbool $
                      DoA "k1" (App (Var "k" 3) (Var "b1" 0)) (Tfunction Tint Any) $
                      DoA "d'" (Binop Add (Var "d" 3) (Vint (-1))) Tint $
                      App (Var "k1" 1) (Var "d'" 0)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . LamA "d" Tint $
      DoA "p'" (App (Var "p" 2) Vunit) (Tfunction Tint (Tlist Any)) $
      DoA "md" (Binop Min (Var "d'" 4) (Var "d" 1)) Tint $
      DoA "xs" (App (Var "p'" 1) (Var "md" 0)) (Tlist Any) $
      Binop ConcatMap (Var "xs" 0) (LamA "vd" (Tpair Any Tint) $ DoA "v" (Unop Fst (Var "vd" 0)) Any $
                                         DoA "rd" (Unop Snd (Var "vd" 1)) Tint $
                                         DoA "consumed" (Binop Minus (Var "md" 4) (Var "rd" 0)) Tint $
                                         DoA "trued" (Binop Minus (Var "d" 7) (Var "consumed" 0)) Tint $
                                         DoA "k'" (App (Var "k" 9) (Var "v" 3)) (Tfunction Tint Any)$
                                         App (Var "k'" 0) (Var "trued" 1)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "d" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any) $
                App (Var "p'" 0) (Var "d" 2)
    , LamA "vs" (Tlist Any) $ Binop ConcatMap (Var "vs" 0) (LamA "vd" (Tpair Any Tint) $
        DoA "v" (Unop Fst (Var "vd" 0)) Any $
        DoA "d" (Unop Snd (Var "vd" 1)) Tint $
        DoA "k'" (App (Var "k" 5) (Var "v" 1)) (Tfunction Tint Any) $
        App (Var "k'" 0) (Var "d" 1))
    )))

tDepthAmbSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Any) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tbool) Tint),
  ("for", Lfor "for" Any)
  ])

tDepthAmbComp1 = HandleA UNone hPureT (HandleA (UList UNone) hAmbT (DoA "f" (HandleA (UList UNone) hDepthAmbT cDepthT) (Tfunction Tint Any) $ App (Var "f" 0) (Vint 2)))
tDepthAmb1 = checkFile tAmbGam tDepthAmbSig tDepthAmbComp1 (Nested (Tpair Tint Tint))

tDepthAmbComp2 = HandleA UNone hPureT (HandleA (UList UNone) hAmbT (DoA "f" (HandleA (UList UNone) hDepthAmb2T cDepthT) (Tfunction Tint Any) $ App (Var "f" 0) (Vint 2)))
tDepthAmb2 = checkFile tAmbGam tDepthAmbSig tDepthAmbComp2 (Nested (Tpair Tint Tint))

