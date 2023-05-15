module ParExamples where

import Syntax
import Shared
import Evaluation
import Prelude hiding ((<>))
import Data.Text.IO
import System.Random

----------------------------------------------------------------
-- Parallel example 

-- | @hAccum@ is an example handler for accumulating a value
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

hPure :: Handler
hPure = Parallel
  (("list", "p", "k", 
      Do "result" (Binop Map (Var "list" 2) (Var "p" 1)) $
      App (Var "k" 1) (Var "result" 0)))
  (("x", Return (Var "x" 0)))
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

----------------------------------------------------------------
-- Weak exceptions example

-- Ideally does not need separate handler for accumulating strings
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


hWeak :: Handler
hWeak = Handler
  "hWeak" ["throw"] [] ["for"]
  ("x", Return (Vsum (Right (Var "x" 0))))
  (\ oplabel -> case oplabel of
    "throw" -> Just ("x", "k", Return (Vsum (Left (Var "x" 1))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" -> (Just ("list", "l", "k",
          Do "results" (App (Var "l" 1) (Var "list" 2)) $ 
          Do "FirstFail" (Unop FirstFail (Var "results" 0)) $
          Case (Var "FirstFail" 0) 
            "error" (Return $ Vsum $ Left (Var "error" 0))
            "t" (App (Var "k" 3) (Var "t" 0))
        ))
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )


cWeak :: Comp
cWeak = Do "_" (Op "accum" (Vstr "start ") ("y" :. Return (Var "y" 0))) $ 
         (For "for" (Vlist [Vstr "1", Vstr "2", Vstr "3", Vstr "4", Vstr "5"])
         ("x" :. (Do "eq2" (Binop Eq (Var "x" 0) (Vstr "2")) $
         If (Var "eq2" 0)   (Do "_" (Op "accum" (Vstr "!") ("y" :. Return (Var "y" 0))) $
                            Do "_" (Op "throw" (Vstr "error") ("y" :. Return (Var "y" 0))) $
                            Op "accum" (Vstr "unreachable") ("y" :. Return (Var "y" 0)))
        (Op "accum" (Var "x" 1) ("y" :. Return (Var "y" 0)))))
        ("x" :. Return (Var "x" 0)))

exWeak :: Comp
exWeak = hPure # hAccumS # hWeak # cWeak

-- Usage:
-- >>> evalFile exWeak
-- Return ("start 1!345", Left "error")


----------------------------------------------------------
-- PRNG example

hPRNG :: Handler
hPRNG = Handler
  "hPRNG" ["sampleUniform"] [] ["for"]
  ("x", Return . Lam "key" $ Return (Var "x" 1))
  (\ oplabel -> case oplabel of
    "sampleUniform" -> Just ("x", "k", Return . Lam "key" $ 
      Do "pair" (Unop Rand (Var "key" 0)) $
      Do "val" (Unop Fst (Var "pair" 0)) $
      Do "key" (Unop Snd (Var "pair" 1)) $
      Do "cont" (App (Var "k" 4) (Var "val" 1)) $ 
      App (Var "cont" 0) (Var "key" 1))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    "for" ->   (Just ("list", "l", "k", Return . Lam "key" $ 
        Do "keys" (Unop SplitKeyPair (Var "key" 0)) $
        Do "key1" (Unop Fst (Var "keys" 0)) $
        Do "key2" (Unop Snd (Var "keys" 1)) $
        Do "key1s" (Binop SplitKey (Var "key1" 1) (Var "list" 6)) $
        Do "for" (App (Var "l" 6) (Var "list" 7)) $
        Do "results" (Binop Zip (Var "for" 0) (Var "key1s" 1)) $
        Do "cont" (App (Var "k" 7) (Var "results" 0)) $
        App (Var "cont" 0) (Var "key2" 4)))
    _ -> Nothing
  )
  ("f", "p", "k", Return . Lam "key" $
        Do "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) $
        App (Var "f" 4) (Var "pk" 0)
  )


cPRNG :: Comp
cPRNG = For "for" (Vlist [Vunit, Vunit, Vunit]) ("y" :. Op "sampleUniform" (Vunit) ("y" :. Return (Var "y" 0))) ("y" :. Return (Var "y" 0))

cPRNGseq :: Comp
cPRNGseq =  Do "1" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Do "2" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Do "3" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

-- Needs new parallel handler to thread keys through correctly
hPureK :: Handler
hPureK = Parallel
  (("list", "p", "k", Return . Lam "keys" $
      Do "results" (Binop Map (Var "list" 2) (Var "p" 1)) $
      Do "resultskeys" (Binop Map (Var "results" 0) (Var "keys" 1)) $
      App (Var "k" 3) (Var "resultskeys" 0)))
  (("x", Return (Var "x" 0)))
  ("f", "p", "k", Return . Lam "key" $
        Do "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) $
        App (Var "f" 4) (Var "pk" 0)
  )

exPRNGpar :: Comp
exPRNGpar = hPure # (Do "key" (Return (Vkey (mkStdGen 42))) $
         Do "ex" (hPureK # hPRNG # cPRNG) $
        (App (Var "ex" 0) (Var "key" 1)))

exPRNGseq :: Comp
exPRNGseq = hPure # (Do "key" (Return (Vkey (mkStdGen 42))) $
         Do "ex" (hPure # hPRNG # cPRNGseq) $
        (App (Var "ex" 0) (Var "key" 1)))


-- Usage:
-- Parallel version
-- >>> evalFile exPRNGpar
-- Return [80, 38, 7]

-- Sequential version
-- >>> evalFile exPRNGseq
-- Return [48, 23, 95]

-- Notice different values, because the keys split in the parallel version

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

--------------------------------------------------------

-- Parallel (accum) example via scoped effect

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


hPureSc :: Handler
hPureSc = Handler
  "hPureSc" [] ["for"] []
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", 
              Do "results" (Binop Map (Var "x" 2) (Var "p" 1)) $
              App (Var "k" 1) (Var "results" 0))
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

----------------------------------------------------------------------------------------------------------------------------

-- Weak exceptions example as scoped effect

-- Ideally does not need separate handler for accumulating strings
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


hWeakSc :: Handler
hWeakSc = Handler
  "hWeak" ["throw"] ["for"] []
  ("x", Return (Vsum (Right (Var "x" 0))))
  (\ oplabel -> case oplabel of
    "throw" -> Just ("x", "k", Return (Vsum (Left (Var "x" 1))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k",
      Do "results" (Sc "for" (Var "x" 2) ("y" :. App (Var "p" 2) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
      Do "FirstFail" (Unop FirstFail (Var "results" 0)) $
      Case (Var "FirstFail" 0) 
        "error" (Return $ Vsum $ Left (Var "error" 0))
        "t" (App (Var "k" 3) (Var "t" 0)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", 
        Do "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) $
        App (Var "f" 3) (Var "pk" 0)
  )

cWeakSc :: Comp
cWeakSc = Do "_" (Op "accum" (Vstr "start ") ("y" :. Return (Var "y" 0))) $ 
         (Sc "for" (Vlist [Vstr "1", Vstr "2", Vstr "3", Vstr "4", Vstr "5"])
         ("x" :. (Do "eq2" (Binop Eq (Var "x" 0) (Vstr "2")) $
         If (Var "eq2" 0)   (Do "_" (Op "accum" (Vstr "!") ("y" :. Return (Var "y" 0))) $
                            Do "_" (Op "throw" (Vstr "error") ("y" :. Return (Var "y" 0))) $
                            Op "accum" (Vstr "unreachable") ("y" :. Return (Var "y" 0)))
        (Op "accum" (Var "x" 1) ("y" :. Return (Var "y" 0)))))
        ("x" :. Return (Var "x" 0)))

exWeakSc :: Comp
exWeakSc = hPureSc # hAccumSSc # hWeakSc # cWeakSc

-- Usage:
-- >>> evalFile exWeakSc
-- Return ("start 1!345", Left "error")

----------------------------------------------------------------------------------------------------------------------------

-- PRNG example as scoped effect

hPRNGSc :: Handler
hPRNGSc = Handler
  "hPRNGSc" ["sampleUniform"] ["for"] []
  ("x", Return . Lam "key" $ Return (Var "x" 1))
  (\ oplabel -> case oplabel of
    "sampleUniform" -> Just ("x", "k", Return . Lam "key" $ 
      Do "pair" (Unop Rand (Var "key" 0)) $
      Do "val" (Unop Fst (Var "pair" 0)) $
      Do "key" (Unop Snd (Var "pair" 1)) $
      Do "cont" (App (Var "k" 4) (Var "val" 1)) $ 
      App (Var "cont" 0) (Var "key" 1))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", Return . Lam "key" $ 
        Do "keys" (Unop SplitKeyPair (Var "key" 0)) $
        Do "key1" (Unop Fst (Var "keys" 0)) $
        Do "key2" (Unop Snd (Var "keys" 1)) $
        Do "key1s" (Binop SplitKey (Var "key1" 1) (Var "list" 6)) $
        Do "for" (Sc "for" (Var "x" 7) ("y" :. App (Var "p" 7) (Var "y" 0)) ("z" :. Return (Var "z" 0))) $
        Do "results" (Binop Zip (Var "for" 0) (Var "key1s" 1)) $
        Do "cont" (App (Var "k" 7) (Var "results" 0)) $
        App (Var "cont" 0) (Var "key2" 4))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "keys" $
        Do "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) $
        App (Var "f" 4) (Var "pk" 0)
  )

cPRNGSc :: Comp
cPRNGSc = Sc "for" (Vlist [Vunit, Vunit, Vunit]) ("y" :. Op "sampleUniform" (Vunit) ("y" :. Return (Var "y" 0))) ("y" :. Return (Var "y" 0))

cPRNGseqSc :: Comp
cPRNGseqSc =  Do "1" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Do "2" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Do "3" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

-- Needs new parallel handler to thread keys through correctly
hPureKSc :: Handler
hPureKSc = Handler
  "hPureSc" [] ["for"] []
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", Return . Lam "keys" $
                Do "results" (Binop Map (Var "x" 3) (Var "p" 2)) $
                Do "resultskeys" (Binop Map (Var "results" 0) (Var "keys" 1)) $
                App (Var "k" 3) (Var "resultskeys" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "keys" $
        Do "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) $
        App (Var "f" 4) (Var "pk" 0)
  )


exPRNGparSc :: Comp
exPRNGparSc = hPureSc # (Do "key" (Return (Vkey (mkStdGen 42))) $
         Do "ex" (hPureKSc # hPRNGSc # cPRNGSc) $
        (App (Var "ex" 0) (Var "key" 1)))


-- Usage:
-- >>> evalFile exPRNGparSc
-- Return [80,38,7]

exPRNGseqSc :: Comp
exPRNGseqSc = hPure # (Do "key" (Return (Vkey (mkStdGen 42))) $
         Do "ex" (hPureSc # hPRNGSc # cPRNGseqSc) $
        (App (Var "ex" 0) (Var "key" 1)))

-- Usage:
-- >>> evalFile exPRNGseqSc
-- Return [48,23,95]

-- Remark that these results are the same as the examples as parallel effects

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

