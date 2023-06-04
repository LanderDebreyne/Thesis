module Inc where

import Syntax
import Once
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing


----------------------------------------------------------------
-- Inc Effect, incrementing counter state (Untyped)

-- | Inc effect handler
-- Increments and passes counter state
-- inc increments the counter by 1
-- the for operation sums the counters of a list of computations and runs the continuation with the sum 
hInc :: Handler
hInc = Handler
  "hInc" ["inc"] [] []
  ("x", Return . Lam "s" $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "inc" -> Just ("_", "k",
      Return . Lam "s" $ Do "k'" (App (Var "k" 1) (Var "s" 0)) $
                         Do "s'" (Binop Add (Var "s" 1) (Vint 1)) $
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
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Unop Fst (Var "zs" 0)) $
                 Do "s'" (Unop Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- | Applying initial counter value
runInc :: Int -> Comp -> Comp
runInc s c = Do "c'" (hInc # c) $ App (Var "c'" 0) (Vint s)

-- | Example program
-- cInc increments the counter by 1
cInc :: Comp
cInc = Op "choose" Vunit ("b" :.
        If (Var "b" 0) (op "inc" Vunit) (op "inc" Vunit))

-- | Example program using for
-- increments the counter by 1 for each element in the list 
cIncFor :: Comp
cIncFor = For "for" (Vlist [Vunit, Vunit, Vunit, Vunit]) ("y" :. op "inc" Vunit) ("z" :. Return (Var "z" 0))

-- Handling @cInc@:
-- >>> evalFile $ hOnce # runInc 0 cInc
-- >>> evalFile $ runInc 0 (hOnce # cInc)
-- Return (Vlist [Vpair (Vint 0,Vint 1),Vpair (Vint 0,Vint 1)])
-- Return (Vpair (Vlist [Vint 0,Vint 1],Vint 2))

-- | Example program that uses forwarding in the evaluation
-- forwards hInc through cFwd to first handle the once operation by hOnce
cFwd :: Comp
cFwd = Sc "once" Vunit ("_" :. cInc) ("x" :. Op "inc" Vunit ("y" :. 
        Do "z" (Binop Add (Var "x" 1) (Var "y" 0)) $ Return (Var "z" 0)))

-- Handling @cFwd@:
-- >>> evalFile $ hOnce # runInc 0 cFwd
-- Return (Vlist [Vpair (Vint 1,Vint 2)])

----------------------------------------------------------------
-- Inc Effect, incrementing counter state (Untyped)


-- | Inc effect handler
-- Increments and passes counter state
-- inc increments the counter by 1
-- for sums the counters of a list of computations and runs the continuation with the sum
hIncT :: Handler
hIncT = Handler
  "hInc" ["inc"] [] []
  ("x", Return . LamA "s" Tint $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "inc" -> Just ("_", "k",
      Return . LamA "s" Tint $ DoA "k'" (App (Var "k" 1) (Var "s" 0)) (Tfunction Tint (Tpair (TVar "tIncA") Tint)) $
                         DoA "s'" (Binop Add (Var "s" 1) (Vint 1)) (Tint) $
                         App (Var "k'" 1) (Var "s'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "s" Tint $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint (Tpair Any Tint))$
                App (Var "p'" 0) (Var "s" 2)
    , LamA "zs" (Tpair Any Tint) $ DoA "z" (Unop Fst (Var "zs" 0)) Any $
                 DoA "s'" (Unop Snd (Var "zs" 1)) Tint $
                 DoA "k'" (App (Var "k" 4) (Var "z" 1)) (Tfunction Tint (Tpair Any Tint)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- | Apply initial value
runIncT :: Int -> Comp -> ValueType -> Comp
runIncT s c vt = DoA "c'" (HandleA (UFunction (UFirst UNone)) hIncT c) (Tfunction Tint vt) $ App (Var "c'" 0) (Vint s)

-- | Typed inc example computation
-- increments the counter by 1
cIncT :: Comp
cIncT = OpA "choose" Vunit (DotA "b" Tbool
        (If (Var "b" 0) (opT "inc" Vunit (TVar "tIncB")) (opT "inc" Vunit (TVar "tIncB"))))

-- | First inc typechecking example
tInc1Gam = Map.fromList([
  ("tIncA", Tint), 
  ("tIncB", (Tlist Tint)),
  ("tOnceA", Tpair Tint Tint)])
tInc1Sig = Map.fromList([
  ("inc", Lop "inc" Tunit Tunit), 
  ("choose", Lop "choose" Tunit Tbool)])
tInc1Comp = (HandleA (UList UNone) (hOnceT) (runIncT 0 cIncT (Tpair (Tlist Tint) Tint)))
tInc1 = checkFile tInc1Gam tInc1Sig tInc1Comp (Tlist (Tpair Tint Tint))

-- | Second inc typechecking example
tInc2Gam = Map.fromList([
  ("tIncA", Tlist Tint), 
  ("tIncB", Tint),
  ("tOnceA", Tint)])
tInc2Comp = runIncT 0 (HandleA (UList UNone) (hOnceT) (cIncT)) (Tpair (Tlist Tint) Tint)
tInc2 = checkFile tInc2Gam tInc1Sig tInc2Comp (Tpair (Tlist Tint) Tint)

-- | Third inc typechecking example
tInc3Sig = Map.fromList([
  ("inc", Lop "inc" Tunit Tunit), 
  ("choose", Lop "choose" Tunit Tbool),
  ("once", Lsc "once" Tunit Tint)])
tInc3Comp = HandleA (UList UNone) (hOnceT) (runIncT 0 cFwdT (Tpair (Tlist Tint) Tint))
tInc3 = checkFile tInc1Gam tInc3Sig tInc3Comp (Tlist (Tpair Tint Tint))

-- | Typed inc example computation using parallel effect
cIncForT :: Comp
cIncForT = ForA "for" (Vlist [Vunit, Vunit, Vunit, Vunit]) (DotA "y" Tunit (opT "inc" Vunit (TVar "tIncB"))) (DotA "z" Any (Return (Var "z" 0)))

-- | Typed example of inc that uses forwarding
cFwdT :: Comp
cFwdT = ScA "once" Vunit (DotA "_" Tunit cIncT) (DotA "x" Tint (OpA "inc" Vunit (DotA "y" Tint
        (DoA "z" (Binop Add (Var "x" 1) (Var "y" 0)) Any $ Return (Var "z" 0)))))

exInc1 = hOnce # runInc 0 cInc
exInc2 = runInc 0 (hOnce # cInc)
exInc3 = hOnce # runInc 0 cFwd




----------------------------------------------------------------

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
 
coinOnce = Do "r" (Sc "once" Vunit ("y" :. exProg) ("z" :. Return (Var "z" 0))) $
            Return (Var "r" 0)