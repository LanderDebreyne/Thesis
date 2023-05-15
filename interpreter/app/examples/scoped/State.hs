module State where

import Syntax
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing


----------------------------------------------------------------
-- Local State Effect (Untyped)

-- State handler
hState :: Handler
hState = Handler
  "hState" ["get", "put"] ["local"] []
  ("x", Return . Lam "m" $ Return (Vpair (Var "x" 1, Var "m" 0)))
  (\ oplabel -> case oplabel of
    "get" -> Just ("x", "k",
      Return . Lam "m" $ Do "v" (Binop Retrieve (Var "x" 2) (Var "m" 0)) $
                         Do "k'" (App (Var "k" 2) (Var "v" 0)) $
                         App (Var "k'" 0) (Var "m" 2))
    "put" -> Just ("pa", "k",
      Return . Lam "m" $ Do "k'" (App (Var "k" 1) Vunit) $
                         Do "m'" (Binop Update (Var "pa" 3) (Var "m" 1)) $
                         App (Var "k'" 1) (Var "m'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "local" -> Just ("xv", "p", "k",
      Return . Lam "m" $ Do "x" (Unop Fst (Var "xv" 3)) $
                         Do "v" (Unop Snd (Var "xv" 4)) $
                         Do "um" (Binop Update (Var "xv" 5) (Var "m" 2)) $
                         Do "p'" (App (Var "p" 5) Vunit) $
                         Do "tm" (App (Var "p'" 0) (Var "um" 1)) $
                         Do "t" (Unop Fst (Var "tm" 0)) $
                         Do "m'" (Unop Snd (Var "tm" 1)) $
                         Do "k'" (App (Var "k" 8) (Var "t" 1)) $
                         Do "oldv" (Binop Retrieve (Var "x" 7) (Var "m" 8)) $
                         Do "newm" (Binop Update (Vpair (Var "x" 8, Var "oldv" 0)) (Var "m'" 2)) $
                         App (Var "k'" 2) (Var "newm" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                 Do "s'" (Unop Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- State example program
cState :: Comp
cState = Do "_" (op "put" (Vpair (Vstr "x", Vint 10))) $
         Do "x1" (sc "local" (Vpair (Vstr "x", Vint 42)) ("_" :. op "get" (Vstr "x"))) $
         Do "x2" (op "get" (Vstr "x")) $
         Return (Vpair (Var "x1" 1, Var "x2" 0))

-- Handling @cState@:
exState :: Comp
exState = Do "m" (Unop Newmem Vunit) $ 
                Do "c" (hState # cState) $
                Do "x" (App (Var "c" 0) (Var "m" 1)) $
                Unop Fst (Var "x" 0)

-- >>> evalFile exState
-- Return (Vpair (Vint 42,Vint 10))

----------------------------------------------
-- Typed State effect

-- Typed state handler
-- Pass, get and put state
hStateT :: Handler
hStateT = Handler
  "hState" ["get", "put"] ["local"] []
  ("x", Return . LamA "m" Tmem $ Return (Vpair (Var "x" 1, Var "m" 0)))
  (\ oplabel -> case oplabel of
    "get" -> Just ("x", "k",
      Return . LamA "m" Tmem $ DoA "v" (Binop Retrieve (Var "x" 2) (Var "m" 0)) Tint $
                         DoA "k'" (App (Var "k" 2) (Var "v" 0)) (Tfunction Tmem (Tpair Any Tmem)) $
                         App (Var "k'" 0) (Var "m" 2))
    "put" -> Just ("pa", "k",
      Return . LamA "m" Tmem $ DoA "k'" (App (Var "k" 1) Vunit) (Tfunction Tmem (Tpair Any Tmem)) $
                         DoA "m'" (Binop Update (Var "pa" 3) (Var "m" 1)) Tmem $
                         App (Var "k'" 1) (Var "m'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "local" -> Just ("xv", "p", "k",
      Return . LamA "m" Tmem $ DoA "x" (Unop Fst (Var "xv" 3)) Tstr $
                         DoA "v" (Unop Snd (Var "xv" 4)) Tint $
                         DoA "um" (Binop Update (Var "xv" 5) (Var "m" 2)) Tmem $
                         DoA "p'" (App (Var "p" 5) Vunit) (Tfunction Tmem (Tpair Tint Tmem)) $
                         DoA "tm" (App (Var "p'" 0) (Var "um" 1)) (Tpair Tint Tmem) $
                         DoA "t" (Unop Fst (Var "tm" 0)) Tint $
                         DoA "m'" (Unop Snd (Var "tm" 1)) Tmem $
                         DoA "k'" (App (Var "k" 8) (Var "t" 1)) (Tfunction Tmem (Tpair (Tpair Tint Tint) Tmem))$
                         DoA "oldv" (Binop Retrieve (Var "x" 7) (Var "m" 8)) (TVar "hStateA") $
                         DoA "newm" (Binop Update (Vpair (Var "x" 8, Var "oldv" 0)) (Var "m'" 2)) Tmem $
                         App (Var "k'" 2) (Var "newm" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "m" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any)$
                App (Var "p'" 0) (Var "m" 2)
    , LamA "zs" (Tpair Any (Tint)) $ DoA "z" (Unop Fst (Var "zs" 0)) Any $
                 DoA "s'" (Unop Snd (Var "zs" 1)) Tint $
                 DoA "k'" (App (Var "k" 4) (Var "z" 1)) (Tfunction Tint Any) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- Typed state example computation
cStateT :: Comp
cStateT = DoA "_" (opT "put" (Vpair (Vstr "x", Vint 10)) Tunit) Tunit $
         DoA "x1" (scT "local" (Vpair (Vstr "x", Vint 42)) "_" Tunit (opT "get" (Vstr "x") Tint) Tint) Tint $
         DoA "x2" (opT "get" (Vstr "x") Tint) Tint $
         Return (Vpair (Var "x1" 1, Var "x2" 0))

-- Typed state example
tStateGam = Map.fromList [("hStateA", Tint)]
tStateSig = Map.fromList [("get", Lop "get" Tstr (Tfunction Tmem (Tpair Tstr Tmem))),
                          ("put", Lop "put" (Tpair Tstr Tint) (Tfunction Tmem (Tpair Tunit Tmem))),
                          ("local", Lsc "local" (Tpair Tstr Tint) Tint)]
handle_cStateT :: Comp
handle_cStateT = DoA "m" (Unop Newmem Vunit) Tmem $ 
                DoA "c" (HandleA (UFunction (UFirst UNone)) hStateT cStateT) (Tfunction Tmem (Tpair (Tpair Tint Tint) Tmem))$
                DoA "x" (App (Var "c" 0) (Var "m" 1)) (Tpair (Tpair Tint Tint) Tmem) $
                Unop Fst (Var "x" 0)

tState = checkFile tStateGam tStateSig handle_cStateT (Tpair Tint Tint)

