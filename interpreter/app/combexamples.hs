module CombExamples where

import Syntax
import Evaluation
import Examples
import Prelude hiding ((<>))
import Data.Text.IO
import System.Random

----------------------------------------------------------------
-- * Section 7.5 : Depth-Bounded Search with Amb

-- | @hDepth@ refers to the @h_depth@ handler in Section 7.5
hDepthAmb :: Handler
hDepthAmb = Handler
  "hDepthAmb" ["choose", "fail"] ["depth"] []
  ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . Lam "d" $
      Do "b" (Binop Eq (Var "d" 0) (Vint 0)) $
      If (Var "b" 0) (Return (Vlist []))
                     (Do "b1" (op "amb" (Vlist [Vbool True, Vbool False])) $
                      Do "k1" (App (Var "k" 3) (Var "b1" 0)) $
                      Do "d'" (Binop Add (Var "d" 3) (Vint (-1))) $
                      App (Var "k1" 1) (Var "d'" 0)))
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

-- | @hDepth2@ is another handler for @depth@.
-- The depth consumed by the scoped computation is also counted in the global depth bound.
hDepthAmb2 :: Handler
hDepthAmb2 = Handler
  "hDepthAmb2" ["choose", "fail"] ["depth"] []
  ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose" -> Just ("x", "k", Return . Lam "d" $
      Do "b" (Binop Eq (Var "d" 0) (Vint 0)) $
      If (Var "b" 0) (Return (Vlist []))
                     (Do "b1" (op "amb" (Vlist [Vbool True, Vbool False])) $
                      Do "k1" (App (Var "k" 3) (Var "b1" 0)) $
                      Do "d'" (Binop Add (Var "d" 3) (Vint (-1))) $
                      App (Var "k1" 1) (Var "d'" 0)))
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


exDepthAmb1 = hPure # hAmb # (Do "f" (hDepthAmb # cDepth) $ App (Var "f" 0) (Vint 2))
exDepthAmb2 = hPure # hAmb # (Do "f" (hDepthAmb2 # cDepth) $ App (Var "f" 0) (Vint 2))

-- evalFileFlat $ hPure # hAmb # (Do "f" (hDepthAmb # cDepth) $ App (Var "f" 0) (Vint 2))
-- evalFileFlat $ hPure # hAmb # (Do "f" (hDepthAmb2 # cDepth) $ App (Var "f" 0) (Vint 2))
