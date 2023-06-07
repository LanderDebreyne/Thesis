module Coins where

import Syntax
import Once
import Evaluation
import Shared
import Inc


-- hTrue
hTrue :: Handler
hTrue = Handler
  "hTrue" ["choose"] [] []
  ("x", Return $ Var "x" 0)
  (\ oplabel -> case oplabel of
    "choose" -> Just ("x", "k",
      App (Var "k" 0) (Vbool True))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMap (Var "z" 0) (Var "k" 1)))

-- hBoth
hBoth :: Handler
hBoth = Handler
  "hBoth" ["choose"] [] []
  ("x", Return $ Vlist [Var "x" 0])
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return $ Vlist [])
    "choose" -> Just ("x", "k",
      Do "xs" (App (Var "k" 0) (Vbool True)) $
      Do "ys" (App (Var "k" 1) (Vbool False)) $
      Binop Append (Var "xs" 1) (Var "xs" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  (lift2fwd ("k", "z", Binop ConcatMap (Var "z" 0) (Var "k" 1)))

-- | Examples for Section 2.2 of the paper
coinFlip = Do "coin" (Op "choose" Vunit ("y" :. If (Var "y" 0) (Return (Vstr "heads")) (Return (Vstr "tails")))) $
          Binop AppendS (Vstr "The coin flip result is ") (Var "coin" 0)

coinTrue = hTrue # coinFlip
coinBoth = hBoth # coinFlip


-- | exCoin example for background Section 2.2.4 of the paper
exCoin = Do "lc1" (App checkCoin (Vpair (Vlist [], Vint 0))) $
         Do "lc2" (App checkCoin (Var "lc1" 0)) $
         Do "lc3" (App checkCoin (Var "lc2" 0)) $
         Do "lc4" (App checkCoin (Var "lc3" 0)) $
         Do "l4" (Unop Fst (Var "lc4" 0)) $
         Do "c4" (Unop Snd (Var "lc4" 1)) $
         Do "3h" (Binop Eq (Var "c6" 0) (Vint 3)) $
          If (Var "3h" 0) 
            (Return (Var "l3" 2))
            (op "fail" Vunit)
           

checkCoin = Lam "lc" $ 
            Do "l" (Unop Fst (Var "lc" 0)) $
            Do "c" (Unop Snd (Var "lc" 1)) $
            Do "b" (Binop Eq (Var "c" 0) (Vint 3)) $ 
            If (Var "b" 0) 
              (Return (Var "lc" 3)) 
              (Do "c1" (App incHeads (Var "c" 1)) $
              Do "t" (Binop Eq (Var "c" 2) (Var "c1" 0)) $
              If (Var "t" 0) 
                (Do "l'" (Binop Append (Vstr "T") (Var "l" 4))$
                Return (Vpair (Var "l'" 0, Var "c1" 2))) 
                (Do "l'" (Binop Append (Vstr "H") (Var "l" 4))$
                Return (Vpair (Var "l'" 0, Var "c1" 2))))

incHeads = Lam "c" $ 
          Do "b" (Do "_" (op "inc" Vunit) $ op "choose" Vunit) $ 
          If (Var "b" 0) 
              (Do "c1" (Binop Add (Var "c" 1) (Vint 1)) $ 
                Return (Var "c1" 0)) 
              (Return (Var "c" 1))


localState = hBoth # runInc 0 exCoin
globalState = runInc 1 (hBoth # exCoin)
 
coinOnce = Do "r" (Sc "once" Vunit ("y" :. exCoin) ("z" :. Return (Var "z" 0))) $
            Return (Var "r" 0)