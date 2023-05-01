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
app2 f v1 v2 = Do "f'" (App f v1) $ App (Var "f'" 0) (shiftV 1 v2)

-- | Generic Algebraic Operation.
op :: Name -> Value -> ValueType -> Comp
op l x t = OpA l x (DotA "y" t (Return (Var "y" 0)))

-- | Generic Scoped Operation.
sc :: Name -> Value -> Dot Name Comp -> Comp
sc l x p = Sc l x p ("z" :. Return (Var "z" 0))

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
      Return . LamA "s" Tint $ DoA "k'" (App (Var "k" 1) (Var "s" 0)) (Tfunction Tint (Tpair (TValVar "tIncA") Tint)) $
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
    ( LamA "y" (Any) $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction (Any) (Tfunction Tint (Tpair (Any) Tint)))$
                App (Var "p'" 0) (Var "s" 2)
    , LamA "zs" (Tpair (Any) (Tint)) $ DoA "z" (Unop Fst (Var "zs" 0)) (TValVar "tIncA") $
                 DoA "s'" (Unop Snd (Var "zs" 1)) Tint $
                 DoA "k'" (App (Var "k" 4) (Var "z" 1)) (Tfunction Tint (Tpair (TValVar "tIncA") Tint)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))



-- | @runInc@ is a macro to help applying the initial count value
runInc1T :: Int -> Comp -> Comp
runInc1T s c = DoA "c'" (HandleA (THandler Tint (Tpair Tint Tint)) hIncT c) (Tfunction Tint (Tpair Tint Tint)) $ App (Var "c'" 0) (Vint s)

runInc2T :: Int -> Comp -> Comp
runInc2T s c = DoA "c'" (HandleA (THandler (Tlist Tint) (Tpair (Tlist Tint) Tint)) hIncT c) (Tfunction Tint (Tpair Tint Tint)) $ App (Var "c'" 0) (Vint s)

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
tInc1Comp = (HandleA (THandler (Tpair Tint Tint) (Tlist (Tpair Tint Tint))) (hOnceT) (runInc1T 0 cIncT))
tInc1 = checkFile tInc1Gam tInc1Sig tInc1Comp (Tlist (Tpair Tint Tint))

tInc2Gam = Map.fromList([
  ("tIncA", Tlist Tint), 
  ("tOnceA", Tint)])
tInc2Comp = runInc2T 0 (HandleA (THandler Tint (Tlist Tint)) (hOnceT) (cIncT))
tInc2 = checkFile tInc2Gam tInc1Sig tInc2Comp (Tpair (Tlist Tint) Tint)

tInc3Sig = Map.fromList([
  ("inc", Lop "inc" Tunit Tunit), 
  ("choose", Lop "choose" Tunit Tbool),
  ("once", Lsc "once" Tunit Tint)])
tInc3Comp = (HandleA (THandler (Tpair Tint Tint) (Tlist (Tpair Tint Tint)))) (hOnceT) (runInc1T 0 cFwdT)
tInc3 = checkFile tInc1Gam tInc3Sig tInc3Comp (Tpair Tint Tint)

cIncForT :: Comp
cIncForT = ForA "for" (Vlist [Vunit, Vunit, Vunit, Vunit]) (DotA "y" Tunit (op "inc" Vunit Any)) (DotA "z" Any (Return (Var "z" 0)))

cFwdT :: Comp
cFwdT = ScA "once" Vunit (DotA "_" Any cIncT) (DotA "x" Tint (OpA "inc" Vunit (DotA "y" Tint
        (DoA "z" (Binop Add (Var "x" 1) (Var "y" 0)) (Tint) $ Return (Var "z" 0)))))

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

-- Handling @cOnce@:
-- >>> evalFile $ hOnce # cOnce
-- Return (Vlist [Vstr "heads"])

tOnceGam = Map.fromList([
  ("tOnceA", Tstr)])
tOnceSig = Map.fromList([
  ("choose", Lop "choose" Tunit Tbool),
  ("once", Lsc "once" Tunit Tbool)])
tOnceComp = HandleA (THandler (Any) (Tlist (Any))) hOnceT cOnceT
tOnce = checkFile tOnceGam tOnceSig tOnceComp (Tlist (TValVar "tOnceA"))
