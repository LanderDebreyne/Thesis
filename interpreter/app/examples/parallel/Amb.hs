module Amb where

import Syntax
import Accum
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing

----------------------------------------------------------
-- Amb example

hAmb :: Handler
hAmb = Handler
  "hAmb" ["amb"][] ["for"]
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    "amb" -> Just ("x", "k",
      For "for" (Var "x" 1) ("y" :. App (Var "k" 1) (Var "y" 0)) ("z" :. Return (Var "z" 0)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    "for" ->   (Just ("list", "l", "k",
        Do "results" (App (Var "l" 1) (Var "list" 2)) $ 
        Do "productElts" (Unop CartesianProd (Var "results" 0)) $
        For "for" (Var "productElts" 0) ("y" :. App (Var "k" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))
      ))
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )


cAmb :: Comp
cAmb = 
  Do "d1" (Op "amb" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5, Vint 6, Vint 7, Vint 8, Vint 9]) ("y" :. Return (Var "y" 0))) $
  Do "d2" (Op "amb" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5, Vint 6, Vint 7, Vint 8, Vint 9]) ("y" :. Return (Var "y" 0))) $
  Do "res" (Binop Add (Var "d1" 1) (Var "d2" 0)) $
  Do "eq" (Binop Eq (Var "res" 0) (Vint 13)) $
  If (Var "eq" 0) (Op "accum" (Vpair (Var "d1" 3, Var "d2" 2)) ("y" :. Return Vunit)) (Return Vunit)


exAmb :: Comp
exAmb = hPure # hAccumL # hAmb # cAmb

-- Usage:
-- >>> evalFile exAmb
-- Return ([(4, 9),(5, 8),(6, 7),(7, 6),(8, 5),(9, 4)], [[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()]])
-- Finds [(4,9),(5,8),(6,7),(7,6),(8,5),(9,4)]


cComb :: Comp
cComb = 
  Do "d1" (Op "amb" (Vlist [Vstr "H", Vstr "T"]) ("y" :. Return (Var "y" 0))) $
  Do "d2" (Op "amb" (Vlist [Vstr "H", Vstr "T"]) ("y" :. Return (Var "y" 0))) $
  Do "d3" (Op "amb" (Vlist [Vstr "H", Vstr "T"]) ("y" :. Return (Var "y" 0))) $
  Do "l1" (Binop AppendS (Var "d1" 2) (Var "d2" 1)) $ 
  Binop AppendS (Var "l1" 0) (Var "d3" 1)

exComb :: Comp
exComb = hPure # hAmb # cComb

-- Usage:
-- >>> evalFile exComb
-- Return [[["HHH","HHT"],["HTH","HTT"]],[["THH","THT"],["TTH","TTT"]]]


----------------------------------------------------------------------------------------------------------------------------

-- Amb example as scoped effect
hAmbSc :: Handler
hAmbSc = Handler
  "hAmbSc" ["amb"] ["for"] []
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    "amb" -> Just ("x", "k",
      Sc "for" (Var "x" 1) ("y" :. App (Var "k" 1) (Var "y" 0)) ("z" :. Return (Var "z" 0)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "results" (Sc "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $ 
              Do "productElts" (Unop CartesianProd (Var "results" 0)) $
              Sc "for" (Var "productElts" 0) ("y" :. App (Var "k" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )


exAmbSc :: Comp
exAmbSc = hPureSc # hAccumScL # hAmbSc # cAmb

-- Usage:
-- >>> evalFile exAmbSc
-- Return ([(4, 9),(5, 8),(6, 7),(7, 6),(8, 5),(9, 4)], [[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()],[(),(),(),(),(),(),(),(),()]])

-- Finds [(4,9),(5,8),(6,7),(7,6),(8,5),(9,4)]

exCombSc :: Comp
exCombSc = hPureSc # hAmbSc # cComb

-- Usage:
-- >>> evalFile exCombSc
-- Return [[["HHH","HHT"],["HTH","HTT"]],[["THH","THT"],["TTH","TTT"]]]

-- Remark that these results are the same as the examples using parallel effects

------------------------------------------------------------------------------------------------------------------  
-- Typed Amb Effect (List Effect)


-- Typed amb handler
-- Evaluates for every value in the input list of values
hAmbT :: Handler
hAmbT = Handler
  "hAmb" ["amb"][] ["for"]
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    "amb" -> Just ("x", "k",
      ForA "for" (Var "x" 1) (DotA "y" Tint (App (Var "k" 1) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    "for" ->   (Just ("list", "l", "k",
        DoA "results" (App (Var "l" 1) (Var "list" 2)) (Tlist Tint) $ 
        DoA "productElts" (Unop CartesianProd (Var "results" 0)) (Tlist Tint) $
        ForA "for" (Var "productElts" 0) (DotA "y" Tint (App (Var "k" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))
      ))
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

-- Typed Accum handler for lists
-- Pass, access and alter an accumulated value
-- Parallel effect
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

-- Typed amb example computation
cAmbT :: Comp
cAmbT = 
  DoA "d1" (OpA "amb" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5, Vint 6, Vint 7, Vint 8, Vint 9]) (DotA "y" Tint (Return (Var "y" 0)))) Tint $
  DoA "d2" (OpA "amb" (Vlist [Vint 1, Vint 2, Vint 3, Vint 4, Vint 5, Vint 6, Vint 7, Vint 8, Vint 9]) (DotA "y" Tint (Return (Var "y" 0)))) Tint $
  DoA "res" (Binop Add (Var "d1" 1) (Var "d2" 0)) Tint $
  DoA "eq" (Binop Eq (Var "res" 0) (Vint 13)) Tbool $
  If (Var "eq" 0) (OpA "accum" (Vpair (Var "d1" 3, Var "d2" 2)) (DotA "y" Tunit (Return Vunit))) (Return Vunit)

-- Typed amb example
tAmbGam = Map.empty
tAmbSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Tint) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tint) Tint),
  ("for", Lfor "for" Any)
  ])
tAmbComp = HandleA UNone hPureT (HandleA (USecond UNone) hAccumLT (HandleA (UList (UList UNone)) hAmbT cAmbT))
tAmb = checkFile tAmbGam tAmbSig tAmbComp (Tpair (Tlist (Tpair Tint Tint)) (Tlist (Tlist Tunit)))

-- Typed amb example computation
cCombT = DoA "d1" (OpA "amb" (Vlist [Vstr "H", Vstr "T"]) (DotA "y" Any (Return (Var "y" 0)))) Tstr $ 
            DoA "d2" (OpA "amb" (Vlist [Vstr "H", Vstr "T"]) (DotA "y" Any (Return (Var "y" 0)))) Tstr $
            DoA "d3" (OpA "amb" (Vlist [Vstr "H", Vstr "T"]) (DotA "y" Any (Return (Var "y" 0)))) Tstr $
            DoA "l1" (Binop AppendS (Var "d1" 2) (Var "d2" 1)) (Tlist Tstr) $
            Binop AppendS (Var "l1" 0) (Var "d3" 1)

-- Typed amb example
tCombSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Tstr) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tstr) Tstr),
  ("for", Lfor "for" Any)
  ])
tCombComp = HandleA UNone hPureT (HandleA (UList UNone) hAmbT cCombT)
tComb = checkFile tAmbGam tCombSig tCombComp (Tlist (Tlist (Tlist Tstr)))


-- Typed amb handler as scoped effect
-- Evaluates for every value in the input list of values
hAmbScT :: Handler
hAmbScT = Handler
  "hAmbSc" ["amb"] ["for"] []
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    "amb" -> Just ("x", "k",
      ScA "for" (Var "x" 1) (DotA "y" Tint (App (Var "k" 1) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0))))
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

-- Typed Accum handler for lists as scoped effect
-- Pass, access and alter an accumulated value
-- Parallel effect
hAccumScLT :: Handler
hAccumScLT = Handler
  "hAccumScL" ["accum"] ["for"] []
  ("x", Return (Vpair (Vlist [], Var "x" 0)))
  (\ oplabel -> case oplabel of
    "accum" -> Just ("x", "k",
      DoA "k'" (App (Var "k" 0) (Vunit)) (Tpair (Tlist Tint) (Tlist Tunit)) $
      DoA "m'" (Unop Fst (Var "k'" 0)) (Tlist Tint) $
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

-- Typed amb as scoped effect example computation
tAmbScSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Tint) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tint) Tint),
  ("for", Lsc "for" Any Any)
  ])

-- Typed amb example 
tAmbScComp = HandleA UNone hPureScT (HandleA (USecond UNone) hAccumScLT (HandleA (UList (UList UNone)) hAmbScT cAmbT))
tAmbSc = checkFile tAmbGam tAmbScSig tAmbScComp (Tpair (Nested (Tpair Tint Tint)) (Nested Tunit))

-- Typed amb example computation
tCombScSig = Map.fromList([
  ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Any) (Tlist Tunit))),
  ("amb", Lop "amb" (Tlist Tstr) Tstr),
  ("for", Lsc "for" Any Any)
  ])

-- Typed amb example 
tCombScComp = HandleA UNone hPureScT (HandleA (UList UNone) hAmbScT cCombT)
tCombSc = checkFile tAmbGam tCombScSig tCombScComp (Nested Tstr)

