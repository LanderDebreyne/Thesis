module Accum where

import Syntax
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing

----------------------------------------------------------------
-- Accum Effect (Untyped)

-- Accum effect handler
-- Accumulates a value
hAccum :: Handler
hAccum = Handler
  "hAccum" ["accum"] [] ["for"]
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" ->     (Just ("list", "l", "k", 
          Do "pairs" (App (Var "l" 1) (Var "list" 2)) $
          Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
          Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
          Do "k'" (App (Var "k" 3) (Var "second" 0)) $
          Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
                                    If (Var "n" 0) (Return (Vint 0)) (Do "h" (Unop Head (Var "l" 1)) $
                                                                      Do "t" (Unop Tail (Var "l" 2)) $
                                                                      Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                                      Do "x" (Binop Add (Var "h" 2) (Var "y" 0)) $
                                                                      Return (Var "x" 0))) 
            (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
            Do "base" (Unop Fst (Var "k'" 2)) $
            Do "k''" (Unop Snd (Var "k'" 3)) $
            Do "res" (Binop Add (Var "base" 1) (Var "rest" 2)) $
            Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )

-- Accum handler for Strings
hAccumS :: Handler
hAccumS = Handler
  "hAccum" ["accum"] [] ["for"]
  ("x", Return (Vpair (Vstr "", Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop AppendS (Var "x" 4) (Var "m'" 1)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" -> (Just ("list", "l", "k", 
          Do "pairs" (App (Var "l" 1) (Var "list" 2)) $
          Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
          Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
          Do "k'" (App (Var "k" 3) (Var "second" 0)) $
          Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
                                If (Var "n" 0) (Return (Vstr "")) (Do "h" (Unop Head (Var "l" 1)) $
                                                                  Do "t" (Unop Tail (Var "l" 2)) $
                                                                  Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                                  Do "x" (Binop AppendS (Var "h" 2) (Var "y" 0)) $
                                                                  Return (Var "x" 0))) 
            (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
            Do "base" (Unop Fst (Var "k'" 2)) $
            Do "k''" (Unop Snd (Var "k'" 3)) $
            Do "res" (Binop AppendS (Var "base" 1) (Var "rest" 2)) $
            Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )

-- Accum handler for lists
hAccumL :: Handler
hAccumL = Handler
  "hAccumL" ["accum"] [] ["for"]
  ("x", Return (Vpair (Vlist [], Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Append (Var "x" 4) (Var "m'" 1)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" ->     (Just ("list", "l", "k", 
          Do "pairs" (App (Var "l" 1) (Var "list" 2)) $
          Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
          Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
          Do "k'" (App (Var "k" 3) (Var "second" 0)) $
          Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
                                    If (Var "n" 0) (Return (Vlist [])) (Do "h" (Unop Head (Var "l" 1)) $
                                                                      Do "t" (Unop Tail (Var "l" 2)) $
                                                                      Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                                      Do "x" (Binop Append (Var "h" 2) (Var "y" 0)) $
                                                                      Return (Var "x" 0))) 
            (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
            Do "base" (Unop Fst (Var "k'" 2)) $
            Do "k''" (Unop Snd (Var "k'" 3)) $
            Do "res" (Binop Append (Var "base" 1) (Var "rest" 2)) $
            Return  $ (Vpair (Var "res" 0, Var "k''" 1 )))))
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )


cAccum :: Comp
cAccum = For "for" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5]) ("y" :. (op "accum" (Var "y" 0))) ("z" :. (Return (Var "z" 0)))

exFor :: Comp
exFor = hPure # hAccum # cAccum

-- Usage:
-- >>> evalFile exFor
-- Return (Vpair (Vint 15,Vlist [Vunit, Vunit, Vunit, Vunit, Vunit]))


-- Example without traverse clausule

-- Accum effect handler without traverse clause
hAccumNoFor :: Handler
hAccumNoFor = Handler
  "hAccum" ["accum"] [] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )

exNoFor :: Comp
exNoFor = hPure # hAccumNoFor # cAccum

-- Each element of the list is treated as a separate computation
-- The result is a list of results of each computation
-- The results are not accumulated

-- Usage:
-- >>> evalFile exNoFor
-- Return (0, [(1, ()),(2, ()),(3, ()),(4, ()),(5, ())])


----------------------------------------------------------------------------------------------------------------
-- Accum example via scoped effect

-- Accum effect handler as scoped effect
hAccumSc1 :: Handler
hAccumSc1 = Handler
  "hAccumSc" ["accum"] ["for"] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "pairs" (Sc "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
              Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
              Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
              Do "k'" (App (Var "k" 3) (Var "second" 0)) $
              Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
              If (Var "n" 0) (Return (Vint 0)) (Do "h" (Unop Head (Var "l" 1)) $
                                                Do "t" (Unop Tail (Var "l" 2)) $
                                                Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                Do "x" (Binop Add (Var "h" 2) (Var "y" 0)) $
                                                Return (Var "x" 0))) 
              (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
              Do "base" (Unop Fst (Var "k'" 2)) $
              Do "k''" (Unop Snd (Var "k'" 3)) $
              Do "res" (Binop Add (Var "base" 1) (Var "rest" 2)) $
              Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )

-- Accum effect handler as scoped effect
hAccumSc2 :: Handler
hAccumSc2 = Handler
  "hAccumSc" ["accum"] ["for"] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "pairs" (For "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
              Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
              Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
              Do "k'" (App (Var "k" 3) (Var "second" 0)) $
              Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
              If (Var "n" 0) (Return (Vint 0)) (Do "h" (Unop Head (Var "l" 1)) $
                                                Do "t" (Unop Tail (Var "l" 2)) $
                                                Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                Do "x" (Binop Add (Var "h" 2) (Var "y" 0)) $
                                                Return (Var "x" 0))) 
              (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
              Do "base" (Unop Fst (Var "k'" 2)) $
              Do "k''" (Unop Snd (Var "k'" 3)) $
              Do "res" (Binop Add (Var "base" 1) (Var "rest" 2)) $
              Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )

-- Accum for string as scoped effect
hAccumSSc :: Handler
hAccumSSc = Handler
  "hAccumSc" ["accum"] ["for"] [] 
  ("x", Return (Vpair (Vstr "", Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop AppendS (Var "x" 4) (Var "m'" 1)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "pairs" (Sc "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
              Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
              Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
              Do "k'" (App (Var "k" 3) (Var "second" 0)) $
              Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
                                    If (Var "n" 0) (Return (Vstr "")) (Do "h" (Unop Head (Var "l" 1)) $
                                                                      Do "t" (Unop Tail (Var "l" 2)) $
                                                                      Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                                      Do "x" (Binop AppendS (Var "h" 2) (Var "y" 0)) $
                                                                      Return (Var "x" 0))) 
                (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
                Do "base" (Unop Fst (Var "k'" 2)) $
                Do "k''" (Unop Snd (Var "k'" 3)) $
                Do "res" (Binop AppendS (Var "base" 1) (Var "rest" 2)) $
                Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )


-- Accum handler for lists as scoped effect
hAccumScL :: Handler
hAccumScL = Handler
  "hAccumScL" ["accum"] ["for"] []
  ("x", Return (Vpair (Vlist [], Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Append (Var "x" 4) (Var "m'" 1)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "pairs" (Sc "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
              Do "first" (Binop Map (Var "pairs" 0) (Lam "l" (Unop Fst (Var "l" 0)))) $
              Do "second" (Binop Map (Var "pairs" 1) (Lam "l" (Unop Snd (Var "l" 0)))) $
              Do "k'" (App (Var "k" 3) (Var "second" 0)) $
              Letrec "reduce" (Lam "l" . Do "n" (Unop Empty (Var "l" 0)) $
              If (Var "n" 0) (Return (Vlist [])) (Do "h" (Unop Head (Var "l" 1)) $
                                                Do "t" (Unop Tail (Var "l" 2)) $
                                                Do "y" (App (Var "reduce" 4) (Var "t" 0)) $
                                                Do "x" (Binop Append (Var "h" 2) (Var "y" 0)) $
                                                Return (Var "x" 0))) 
              (Do "rest" (App (Var "reduce" 0) (Var "first" 3)) $
              Do "base" (Unop Fst (Var "k'" 2)) $
              Do "k''" (Unop Snd (Var "k'" 3)) $
              Do "res" (Binop Append (Var "base" 1) (Var "rest" 2)) $
              Return  $ (Vpair (Var "res" 0, Var "k''" 1 ))))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )

-- cAccum example rewritten as scoped effect
cAccumSc :: Comp
cAccumSc = Sc "for" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5]) ("y" :. (op "accum" (Var "y" 0))) ("z" :. (Return (Var "z" 0)))

-- cAccumSc example handled by handler that uses scoped effect for pure for handling
exForSc1 :: Comp
exForSc1 = hPureSc # hAccumSc1 # cAccumSc

-- Usage:
-- evalFile exForSc1
-- Return (15, [(),(),(),(),()])

-- cAccumSc example handled by handler that uses parallel effect for pure for handling
exForSc2 :: Comp
exForSc2 = hPure # hAccumSc2 # cAccumSc

-- Usage:
-- evalFile exForSc2
-- Return (15, [(),(),(),(),()])

hAccumScNoFor :: Handler
hAccumScNoFor = Handler
  "hAccumSc" ["accum"] [] []
  ("x", Return (Vpair (Vint 0, Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      Do "k'" (App (Var "k" 0) (Vunit)) $
      Do "m'" (Unop Fst (Var "k'" 0)) $
      Do "s" (Unop Snd (Var "k'" 1)) $
      Do "m''" (Binop Add (Var "m'" 1) (Var "x" 4)) $
      Return (Vpair (Var "m''" 0, Var "s" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )


exNoForSc :: Comp
exNoForSc = hPureSc # hAccumScNoFor # cAccumSc

-- Usage:
-- evalFile exNoForSc
-- Return (0, [(1, ()),(2, ()),(3, ()),(4, ()),(5, ())])

-- Remark that all cAccum examples find the same solution as their parallel effect counterparts


---------------------------------------------------------------------------------------------------------------
-- Typed parallel Accum effect

-- Typed Accum handler for integers
-- Pass, access and alter an accumulated value
-- Parallel effect
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


-- Typed Accum handler for strings
-- Pass, access and alter an accumulated value
-- Parallel effect
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


-- Typed example accum computation
cAccumT :: Comp
cAccumT = ForA "for" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5]) (DotA "y" Tint (opT "accum" (Var "y" 0) Tint)) (DotA "z" Any (Return (Var "z" 0)))

-- Typed Accum handler for integers without defined for
-- Pass, access and alter an accumulated value
-- Without the parallel effect to illustrate the impact of the effect
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

-- Accum example
tAccumGam = Map.empty
tAccumSig = Map.fromList([
  ("accum", Lop "accum" Tint (Tpair Tint Tunit)),
  ("for", Lfor "for" Any)
  ])
tAccumComp1 = HandleA UNone hPureT (HandleA  (USecond UNone) hAccumT cAccumT)
tAccum1 = checkFile tAccumGam tAccumSig tAccumComp1 (Tpair Tint (Tlist Tunit))

-- Accum example without parallel effect
tAccumComp2 = HandleA UNone hPureT (HandleA (USecond UNone) hAccumNoForT cAccumT)
tAccum2 = checkFile tAccumGam tAccumSig tAccumComp2 (Tpair Tint (Tlist (Tpair Tint Tunit)))

tAccumSigSc = Map.fromList([
  ("accum", Lop "accum" Tint (Tpair Tint Tunit)),
  ("for", Lsc "for" (Tlist Any)  Any)
  ])

-- Accum example as scoped effect
tAccumComp3 = HandleA UNone hPureScT (HandleA (USecond UNone) hAccumSc1T cAccumScT)
tAccum3 = checkFile tAccumGam tAccumSigSc tAccumComp3 (Tpair Tint (Tlist Tunit))

-- Accum example as scoped effect without parallel effect
tAccumComp4 = HandleA UNone hPureScT (HandleA (USecond UNone) hAccumScNoForT cAccumScT)
tAccum4 = checkFile tAccumGam tAccumSigSc tAccumComp4 (Tpair Tint (Tlist (Tpair Tint Tunit)))


-- Typed Accum handler for integers as scoped effect
-- Pass, access and alter an accumulated value
-- Parallel effect
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

-- Typed Accum handler for strings as scoped effect
-- Pass, access and alter an accumulated value
-- Parallel effect
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

-- Example Accum computation as scoped effect
cAccumScT :: Comp
cAccumScT = ScA "for" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5]) (DotA "y" Tint (opT "accum" (Var "y" 0) Tint)) (DotA "z" Any (Return (Var "z" 0)))

-- Typed Accum handler for integers as scoped effect
-- Pass, access and alter an accumulated value
-- Without parallel effect
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