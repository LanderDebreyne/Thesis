module Depth where

import Syntax
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing

----------------------------------------------------------------
-- Depth-Bounded Search Effect (Untyped)

-- | Depth-Bounded Search handler
-- The depth bound is passed as an argument to the handler.
-- The depth consumed by the scoped computation is not counted in the global depth bound.
-- choose calculates all possible results, but only if the depth bound is not exceeded.
-- depth calculates all possible results that do not exceed the depth bound.
hDepth :: Handler
hDepth = Handler
  "hDepth" ["choose", "fail"] ["depth"] []
  ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . Lam "d" $
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
  (\ forlabel -> case forlabel of 
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

-- | Depth-Bounded Search handler
-- The depth bound is passed as an argument to the handler.
-- The depth consumed by the scoped computation is also counted in the global depth bound.
-- choose calculates all possible results, but only if the depth bound is not exceeded.
-- depth calculates all possible results that do not exceed the depth bound.
hDepth2 :: Handler
hDepth2 = Handler
  "hDepth" ["choose", "fail"] ["depth"] []
  ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . Lam "d" $
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
  (\ forlabel -> case forlabel of
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


-- | Depth bounded search example program
-- Finds results of depth 1 
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

---------------------------------------------------------------------------------------------------------------------------
-- Typed Bounded Depth First Search effect

-- | Typed bounded depth first search handler
-- Does not restart depth bound in the continuation
-- Does not take into account consumed depth in scoped computation
-- choose calculates all possible results, but only if the depth bound is not exceeded.
-- depth calculates all possible results that do not exceed the depth bound.
hDepthT :: Handler
hDepthT = Handler
  "hDepth" ["choose", "fail"] ["depth"] []
  ("x", Return . LamA "d" Tint $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . LamA "d" Tint $
      DoA "b" (Binop Eq (Var "d" 0) (Vint 0)) Tbool $
      If (Var "b" 0) (Return (Vlist []))
                     (DoA "k1" (App (Var "k" 2) (Vbool True)) (Tfunction Tint (Tlist (Tpair Tint Tint)))$
                      DoA "k2" (App (Var "k" 3) (Vbool False)) (Tfunction Tint (Tlist (Tpair Tint Tint)))$
                      DoA "d'" (Binop Add (Var "d" 3) (Vint (-1))) Tint $
                      DoA "xs" (App (Var "k1" 2) (Var "d'" 0)) (Tlist (Tpair Tint Tint)) $
                      DoA "ys" (App (Var "k2" 2) (Var "d'" 1)) (Tlist (Tpair Tint Tint)) $
                      Binop Append (Var "xs" 1) (Var "ys" 0) ))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . LamA "d" Tint $
      DoA "p'" (App (Var "p" 2) Vunit) (Tfunction Tint (Tlist (Tpair Tint Tint))) $
      DoA "xs" (App (Var "p'" 0) (Var "d'" 4)) (Tlist (Tpair Tint Tint)) $
      Binop ConcatMap (Var "xs" 0) (LamA "v_" (Tpair Tint Tint) $ DoA "v" (Unop Fst (Var "v_" 0)) Tint $
                                         DoA "k'" (App (Var "k" 5) (Var "v" 0)) (Tfunction Tint (Tlist (Tpair Tint Tint)))$
                                         App (Var "k'" 0) (Var "d" 5)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "d" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any) $
                App (Var "p'" 0) (Var "d" 2)
    , LamA "vs" Any $ Binop ConcatMap (Var "vs" 0) (LamA "vd" (Tpair Tint Tint) $
        DoA "v" (Unop Fst (Var "vd" 0)) Tint $
        DoA "d" (Unop Snd (Var "vd" 1)) Tint $
        DoA "k'" (App (Var "k" 5) (Var "v" 1)) (Tfunction Tint Tint) $
        App (Var "k'" 0) (Var "d" 1))
    )))

-- | Typed bounded depth first search handler
-- Does not restart depth bound in the continuation
-- Takes into account consumed depth in scoped computation
-- choose calculates all possible results, but only if the depth bound is not exceeded.
-- depth calculates all possible results that do not exceed the depth bound.
hDepth2T :: Handler
hDepth2T = Handler
  "hDepth" ["choose", "fail"] ["depth"] []
  ("x", Return . LamA "d" Tint $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . LamA "d" Tint $
      DoA "b" (Binop Eq (Var "d" 0) (Vint 0)) Tbool $
      If (Var "b" 0) (Return (Vlist []))
                     (DoA "k1" (App (Var "k" 2) (Vbool True)) (Tfunction Tint (Tlist (Tpair Tint Tint))) $
                      DoA "k2" (App (Var "k" 3) (Vbool False)) (Tfunction Tint (Tlist (Tpair Tint Tint)))$
                      DoA "d'" (Binop Add (Var "d" 3) (Vint (-1))) Tint $
                      DoA "xs" (App (Var "k1" 2) (Var "d'" 0)) (Tlist (Tpair Tint Tint)) $
                      DoA "ys" (App (Var "k2" 2) (Var "d'" 1)) (Tlist (Tpair Tint Tint)) $
                      Binop Append (Var "xs" 1) (Var "ys" 0) ))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . LamA "d" Tint $
      DoA "p'" (App (Var "p" 2) Vunit) (Tfunction Tint (Tlist (Tpair Tint Tint))) $
      DoA "md" (Binop Min (Var "d'" 4) (Var "d" 1)) Tint $
      DoA "xs" (App (Var "p'" 1) (Var "md" 0)) (Tlist (Tpair Tint Tint)) $
      Binop ConcatMap (Var "xs" 0) (LamA "vd" (Tpair Tint Tint) $ DoA "v" (Unop Fst (Var "vd" 0)) Tint $
                                         DoA "rd" (Unop Snd (Var "vd" 1)) Tint $
                                         DoA "consumed" (Binop Minus (Var "md" 4) (Var "rd" 0)) Tint $
                                         DoA "trued" (Binop Minus (Var "d" 7) (Var "consumed" 0)) Tint $
                                         DoA "k'" (App (Var "k" 9) (Var "v" 3)) (Tfunction Tint (Tlist (Tpair Tint Tint)))$
                                         App (Var "k'" 0) (Var "trued" 1)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "d" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any) $
                App (Var "p'" 0) (Var "d" 2)
    , LamA "vs" Any $ Binop ConcatMap (Var "vs" 0) (LamA "vd" (Tpair Tint Tint) $
        DoA "v" (Unop Fst (Var "vd" 0)) Tint $
        DoA "d" (Unop Snd (Var "vd" 1)) Tint $
        DoA "k'" (App (Var "k" 5) (Var "v" 1)) (Tfunction Tint Any) $
        App (Var "k'" 0) (Var "d" 1))
    )))

-- | Typed depth example computation
-- Finds results of depth 1
cDepthT :: Comp
cDepthT = ScA "depth" (Vint 1) (DotA "_" Tunit
 (DoA "b" (opT "choose" Vunit Tbool) Tbool $
 If (Var "b" 0) (Return (Vint 1))
                ( DoA "b'" (opT "choose" Vunit Tbool) Tbool $
                  If (Var "b'" 0)
                     (Return (Vint 2))
                     (Return (Vint 3)))))
  (DotA "x" Tint (DoA "b" (opT "choose" Vunit Tbool) Tbool $
   If (Var "b" 0) (Return (Var "x" 1))
                  ( DoA "b'" (opT "choose" Vunit Tbool) Tbool $
                    If (Var "b'" 0)
                       (Return (Vint 4))
                       (DoA "b''" (opT "choose" Vunit Tbool) Tbool $
                         If (Var "b''" 0)
                            (Return (Vint 5))
                            (Return (Vint 6))))))

-- | First typed depth typechecking example
-- Uses first typed depth handler, which does not take into account consumed depth in scoped computation
tDepthGam = Map.empty
tDepthSig = Map.fromList([
  ("depth", Lsc "depth" Tint Tint),
  ("choose", Lop "choose" Tunit Tbool),
  ("fail", Lop "fail" Tunit Tunit)
  ])

tDepthComp1 = DoA "f" (HandleA (UFunction (UList (UFirst UNone))) hDepthT cDepthT) (Tfunction Tint (Tlist (Tpair Tint Tint))) $ App (Var "f" 0) (Vint 2)
tDepth1 = checkFile tDepthGam tDepthSig tDepthComp1 (Tlist (Tpair Tint Tint))

-- | Second typed depth typechecking example
-- Uses second typed depth handler, which does take into account consumed depth in scoped computation
tDepthComp2 = DoA "f" (HandleA (UFunction (UList (UFirst UNone))) hDepth2T cDepthT) (Tfunction Tint (Tlist (Tpair Tint Tint))) $ App (Var "f" 0) (Vint 2)
tDepth2 = checkFile tDepthGam tDepthSig tDepthComp2 (Tlist (Tpair Tint Tint))

exDepth1 = Do "f" (hDepth # cDepth) $ App (Var "f" 0) (Vint 2)
exDepth2 = Do "f" (hDepth2 # cDepth) $ App (Var "f" 0) (Vint 2)
