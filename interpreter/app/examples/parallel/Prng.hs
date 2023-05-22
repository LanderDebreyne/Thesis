module Prng where

import Syntax
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing
import System.Random

----------------------------------------------------------
-- PRNG example

-- | PRNG handler
-- Picks a random number
-- Works in parallel computations by splitting the keys
-- Works in sequential computations by threading the keys through
-- sampleUniform returns a random number
-- for runs a computation for each element in a list and splits the keys
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


-- | PRNG example computation
-- Picks 3 random numbers in parallel
cPRNG :: Comp
cPRNG = For "for" (Vlist [Vunit, Vunit, Vunit]) ("y" :. Op "sampleUniform" (Vunit) ("y" :. Return (Var "y" 0))) ("y" :. Return (Var "y" 0))

-- | PRNG example computation
-- Picks 3 random numbers sequentially
cPRNGseq :: Comp
cPRNGseq =  Do "1" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Do "2" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Do "3" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

-- | Pure handler that also threads prng keys through
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

----------------------------------------------------------------------------------------------------------------------------

-- | PRNG handler as scoped effect
-- Picks a random number
-- Works in parallel computations by splitting the keys
-- Works in sequential computations by threading the keys through
-- sampleUniform returns a random number
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

-- | PRNG example computation as scoped effect
-- Picks 3 random numbers in parallel
cPRNGSc :: Comp
cPRNGSc = Sc "for" (Vlist [Vunit, Vunit, Vunit]) ("y" :. Op "sampleUniform" (Vunit) ("y" :. Return (Var "y" 0))) ("y" :. Return (Var "y" 0))

-- | PRNG example computation as scoped effect
-- Picks 3 random numbers sequentially
cPRNGseqSc :: Comp
cPRNGseqSc =  Do "1" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Do "2" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Do "3" (Op "sampleUniform" Vunit ("y" :. Return (Var "y" 0))) $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

-- | Pure handler that also threads prng keys through as scoped effect
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

---------------------------------------------------------------------------------------------------------------------------------------
-- Typed Pseudo Random Number Generator Example

-- | Typed prng handler
-- Outputs pseudo random numbers
-- Works in parallel computations by splitting the keys
-- Works in sequential computations by threading the keys through
-- sampleUniform returns a random number
hPRNGT :: Handler
hPRNGT = Handler
  "hPRNG" ["sampleUniform"] [] ["for"]
  ("x", Return . LamA "key" Tkey $ Return (Var "x" 1))
  (\ oplabel -> case oplabel of
    "sampleUniform" -> Just ("x", "k", Return . LamA "key" Tkey $ 
      DoA "pair" (Unop Rand (Var "key" 0)) (Tpair Tint Tkey) $
      DoA "val" (Unop Fst (Var "pair" 0)) Tint $
      DoA "key" (Unop Snd (Var "pair" 1)) Tkey $
      DoA "cont" (App (Var "k" 4) (Var "val" 1)) (Tfunction Tkey (Nested Tint)) $ 
      App (Var "cont" 0) (Var "key" 1))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    "for" ->   (Just ("list", "l", "k", Return . LamA "key" Tkey $ 
        DoA "keys" (Unop SplitKeyPair (Var "key" 0)) (Tpair Tkey Tkey) $
        DoA "key1" (Unop Fst (Var "keys" 0)) Tkey $
        DoA "key2" (Unop Snd (Var "keys" 1)) Tkey $
        DoA "key1s" (Binop SplitKey (Var "key1" 1) (Var "list" 6)) (Tlist Tkey) $
        DoA "for" (App (Var "l" 6) (Var "list" 7)) (Tlist (Tfunction Tkey (Tlist Tint)))$
        DoA "results" (Binop Zip (Var "for" 0) (Var "key1s" 1)) (Tlist Tint) $
        DoA "cont" (App (Var "k" 7) (Var "results" 0)) (Tfunction Tkey (Tlist Tint)) $
        App (Var "cont" 0) (Var "key2" 4)))
    _ -> Nothing
  )
  ("f", "p", "k", Return . LamA "key" Tkey $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )

-- | Typed parallel prng example computation
-- Picks 3 random numbers in parallel
cPRNGT :: Comp
cPRNGT = ForA "for" (Vlist [Vunit, Vunit, Vunit]) (DotA "y" Tunit (OpA "sampleUniform" (Vunit) (DotA "y" Tint (Return (Var "y" 0))))) (DotA "z" Any (Return (Var "z" 0)))

-- | Typed sequential prng example computation
-- Picks 3 random numbers sequentially
cPRNGseqT :: Comp
cPRNGseqT = DoA "1" (OpA "sampleUniform" (Vunit) (DotA "y" Tint (Return (Var "y" 0)))) Tint $
            DoA "2" (OpA "sampleUniform" (Vunit) (DotA "y" Tint (Return (Var "y" 0)))) Tint $
            DoA "3" (OpA "sampleUniform" (Vunit) (DotA "y" Tint (Return (Var "y" 0)))) Tint $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

-- | Typed pure handler that also threads prng keys through
-- Typed pure parallel handler that also threads prng keys through
hPureKT :: Handler
hPureKT = Parallel
  (("list", "p", "k", Return . LamA "keys" (Tlist Tkey) $
      DoA "results" (Binop Map (Var "list" 2) (Var "p" 1)) (Tlist (Tfunction Tkey Any))$
      DoA "resultskeys" (Binop Map (Var "results" 0) (Var "keys" 1)) (Tlist Any) $
      App (Var "k" 3) (Var "resultskeys" 0)))
  (("x", Return (Var "x" 0)))
  ("f", "p", "k", Return . LamA "key" Tkey $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )

-- | Typed parallel prng typechecking example
tPRNGGam = Map.empty
tPRNGSig = Map.fromList([
  ("sampleUniform", Lop "sampleUniform" Tunit (Tfunction Tkey (Nested Tint))),
  ("for", Lfor "for" Any)
  ])
tPRNGComp1 = HandleA UNone hPureT (DoA "key" (Return (Vkey (mkStdGen 42))) Tkey $ DoA "ex" (HandleA UNone hPureKT (HandleA (UFunction UNone) hPRNGT cPRNGT)) (Tfunction Tkey Any) $ App (Var "ex" 0) (Var "key" 1))
tPRNG1 = checkFile tPRNGGam tPRNGSig tPRNGComp1 (Tlist Tint)

-- Typed sequential prng example
tPRNGComp2 = HandleA UNone hPureT (DoA "key" (Return (Vkey (mkStdGen 42))) Tkey $ DoA "ex" (HandleA UNone hPureT (HandleA (UFunction UNone) hPRNGT cPRNGseqT)) (Tfunction Tkey Any) $ App (Var "ex" 0) (Var "key" 1))
tPRNG2 = checkFile tPRNGGam tPRNGSig tPRNGComp2 (Tlist Tint)

-- | Typed prng handler as scoped effect
-- Outputs pseudo random numbers
-- Works in parallel computations by splitting the keys
-- Works in sequential computations by threading the keys through
-- sampleUniform returns a random number
hPRNGScT :: Handler
hPRNGScT = Handler
  "hPRNGSc" ["sampleUniform"] ["for"] []
  ("x", Return . LamA "key" Tkey $ Return (Var "x" 1))
  (\ oplabel -> case oplabel of
    "sampleUniform" -> Just ("x", "k", Return . LamA "key" Tkey $ 
      DoA "pair" (Unop Rand (Var "key" 0)) (Tpair Tint Tkey) $
      DoA "val" (Unop Fst (Var "pair" 0)) Tint $
      DoA "key" (Unop Snd (Var "pair" 1)) Tkey $
      DoA "cont" (App (Var "k" 4) (Var "val" 1)) (Tfunction Tkey (Nested Tint)) $ 
      App (Var "cont" 0) (Var "key" 1))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", Return . LamA "key" Tkey $ 
        DoA "keys" (Unop SplitKeyPair (Var "key" 0)) (Tpair Tkey Tkey) $
        DoA "key1" (Unop Fst (Var "keys" 0)) Tkey $
        DoA "key2" (Unop Snd (Var "keys" 1)) Tkey $
        DoA "key1s" (Binop SplitKey (Var "key1" 1) (Var "list" 6)) (Tlist Tkey) $
        DoA "for" (ScA "for" (Var "x" 7) (DotA "y" Any (App (Var "p" 7) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))) (Tlist (Tfunction Tkey (Tlist Tint)))$
        DoA "results" (Binop Zip (Var "for" 0) (Var "key1s" 1)) (Tlist Tint) $
        DoA "cont" (App (Var "k" 7) (Var "results" 0)) (Tfunction Tkey (Nested Tint)) $
        App (Var "cont" 0) (Var "key2" 4))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "keys" (Tlist Tkey) $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )

-- | Typed parallel prng as scoped effect example
cPRNGScT :: Comp
cPRNGScT = ScA "for" (Vlist [Vunit, Vunit, Vunit]) (DotA "y" Tint (OpA "sampleUniform" (Vunit) (DotA "y" Tint (Return (Var "y" 0))))) (DotA "z" Any (Return (Var "z" 0)))

-- | Typed sequential prng as scoped effect example
cPRNGseqScT :: Comp
cPRNGseqScT =  DoA "1" (OpA "sampleUniform" (Vunit) (DotA "y" Tint (Return (Var "y" 0)))) Tint $
            DoA "2" (OpA "sampleUniform" (Vunit) (DotA "y" Tint (Return (Var "y" 0)))) Tint $
            DoA "3" (OpA "sampleUniform" (Vunit) (DotA "y" Tint (Return (Var "y" 0)))) Tint $
            Return (Vlist [Var "1" 2, Var "2" 1, Var "3" 0])

-- | Typed pure handler that also threads prng keys through as scoped effect
-- Typed pure handler as scoped effect that also threads prng keys through
hPureKScT :: Handler
hPureKScT = Handler
  "hPureSc" [] ["for"] []
  ("x", Return (Var "x" 0))
  (\ oplabel -> case oplabel of
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k", Return . LamA "keys" (Tlist Tkey) $
                DoA "results" (Binop Map (Var "x" 3) (Var "p" 2)) (Tlist Tint) $
                DoA "resultskeys" (Binop Map (Var "results" 0) (Var "keys" 1)) (Tlist Tint) $
                App (Var "k" 3) (Var "resultskeys" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "keys" (Tlist Tkey) $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )

-- | Typed parallel prng as scoped effect typechecking example
tPRNGGamSc = Map.empty
tPRNGSigSc = Map.fromList([
  ("sampleUniform", Lop "sampleUniform" Tunit (Tfunction Tkey (Nested Tint))),
  ("for", Lsc "for" Any Any)
  ])
tPRNGComp3 = HandleA UNone hPureScT (DoA "key" (Return (Vkey (mkStdGen 42))) Tkey $ DoA "ex" (HandleA UNone hPureKScT (HandleA (UFunction UNone) hPRNGScT cPRNGScT)) (Tfunction Tkey Any) $ App (Var "ex" 0) (Var "key" 1))
tPRNG3 = checkFile tPRNGGamSc tPRNGSigSc tPRNGComp3 (Tlist Tint)

-- | Typed sequential prng as scoped effect typechecking example
tPRNGComp4 = HandleA UNone hPureT (DoA "key" (Return (Vkey (mkStdGen 42))) Tkey $ DoA "ex" (HandleA UNone hPureScT (HandleA (UFunction UNone) hPRNGScT cPRNGseqScT)) (Tfunction Tkey Any) $ App (Var "ex" 0) (Var "key" 1))
tPRNG4 = checkFile tPRNGGamSc tPRNGSigSc tPRNGComp4 (Tlist Tint)