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
    , LamA "vs" Any $ Binop ConcatMap (Var "vs" 0) (Lam "vd" $
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



