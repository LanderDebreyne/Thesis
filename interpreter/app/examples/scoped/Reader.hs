module Reader where

import Syntax
import Evaluation
import Shared
import qualified Data.Map as Map
import Typing

----------------------------------------------------------------
-- | Reader effect
-- ask retrieves the reader value
-- local alters the reader value
-- @hReader@ is a reader handler
hReader :: Handler
hReader = Handler
  "hReader" ["ask"] ["local"] []
  ("x", Return . Lam "m" $ Return (Vpair (Var "x" 1, Var "m" 0)))
  (\ oplabel -> case oplabel of
    "ask" -> Just ("_", "k",
      Return . Lam "m" $ Do "env" (Binop Retrieve (Vstr "readerEnv") (Var "m" 0)) $
                         Do "k'" (App (Var "k" 2) (Var "env" 0)) $
                         App (Var "k'" 0) (Var "m" 2))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "local" -> Just ("x", "p", "k",
      Return . Lam "m" $ Do "envKey" (Return (Vstr "readerEnv")) $
                         Do "oldEnv" (Binop Retrieve (Var "envKey" 0) (Var "m" 1)) $
                         Do "newEnv" (App (Var "x" 5) (Var "oldEnv" 0)) $ 
                         Do "um" (Binop Update (Vpair ((Var "envKey" 2), (Var "newEnv" 0))) (Var "m" 3)) $
                         Do "p'" (App (Var "p" 6) Vunit) $
                         Do "tm" (App (Var "p'" 0) (Var "um" 1)) $
                         Do "t" (Unop Fst (Var "tm" 0)) $
                         Do "m'" (Unop Snd (Var "tm" 1)) $
                         Do "k'" (App (Var "k" 9) (Var "t" 1)) $
                         Do "newm" (Binop Update (Vpair ((Var "envKey" 8), (Var "oldEnv" 7))) (Var "m'" 1)) $
                         App (Var "k'" 1) (Var "newm" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "m" $
        Do "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) $
        App (Var "f" 4) (Var "pk" 0)
  )


-- | cReader is an example reader effect program
-- asks for the reader value and alters it locally
cReader :: Comp
cReader = Do "x1" (op "ask" Vunit) $
          Do "x2" ((sc "local" (Lam "x" (Binop Append (Var "x" 0) (Vlist [Vint 5])))) ("_" :. op "ask" Vunit)) $
          Do "x3" (op "ask" Vunit) $ 
          Return (Vpair ((Vpair (Var "x1" 0, Var "x3" 1)), (Var "x3" 2)))

-- | @runReader@ is a macro to help applying the initial reader value
runReader :: Value -> Comp -> Comp
runReader s c = Do "x3" ((sc "local" s) ("_" :. c)) $ 
                Return (Var "x3" 0)

-- | Handling @cReader@:
handle_cReader :: Value -> Comp
handle_cReader c = Do "m" (Unop Newmem (Vunit)) $
                   Do "m" (Binop Update (Vpair ((Vstr "readerEnv"), (Vlist [Vint 1, Vint 2, Vint 3, Vint 4]))) (Var "m" 0)) $
                   Do "c" (hReader # (runReader (c) cReader)) $
                   Do "x" (App (Var "c" 0) (Var "m" 1)) $
                   Unop Fst (Var "x" 0)

-- | @cReader@ example:
exReader :: Comp
exReader = handle_cReader (Lam "x" (Return (Vlist [Vint 1, Vint 2, Vint 3, Vint 4])))

-- Usage:
-- >>> evalFile example_cReader
-- Return (Vpair (Vpair (Vlist [Vint 1,Vint 2,Vint 3,Vint 4],Vlist [Vint 1,Vint 2,Vint 3,Vint 4,Vint 5]),Vlist [Vint 1,Vint 2,Vint 3,Vint 4]))

------------------------------------------------------------------------
-- Typed reader example

-- | Typed reader example
-- ask retrieves the reader value
-- local alters the reader value
hReaderT :: Handler
hReaderT = Handler
  "hReader" ["ask"] ["local"] []
  ("x", Return . LamA "m" Tmem $ Return (Vpair (Var "x" 1, Var "m" 0)))
  (\ oplabel -> case oplabel of
    "ask" -> Just ("_", "k",
      Return . LamA "m" Tmem $ DoA "env" (Binop Retrieve (Vstr "readerEnv") (Var "m" 0)) (Tlist Tint) $
                         DoA "k'" (App (Var "k" 2) (Var "env" 0)) (Tfunction Tmem Any) $
                         App (Var "k'" 0) (Var "m" 2))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "local" -> Just ("x", "p", "k",
      Return . LamA "m" Tmem $ DoA "envKey" (Return (Vstr "readerEnv")) Tstr $
                         DoA "oldEnv" (Binop Retrieve (Var "envKey" 0) (Var "m" 1)) (Tlist Tint) $
                         DoA "newEnv" (App (Var "x" 5) (Var "oldEnv" 0)) (Tlist Tint) $ 
                         DoA "um" (Binop Update (Vpair ((Var "envKey" 2), (Var "newEnv" 0))) (Var "m" 3)) Tmem $
                         DoA "p'" (App (Var "p" 6) Vunit) (Tfunction Tmem (Tpair (Tlist Tint) Tmem)) $
                         DoA "tm" (App (Var "p'" 0) (Var "um" 1)) (Tpair (Tlist Tint) Tmem) $
                         DoA "t" (Unop Fst (Var "tm" 0)) (Tlist Tint) $
                         DoA "m'" (Unop Snd (Var "tm" 1)) Tmem $
                         DoA "k'" (App (Var "k" 9) (Var "t" 1)) (Tfunction Tmem (Tpair (Tpair ( Tpair (Tlist Tint) (Tlist Tint)) (Tlist Tint)) Tmem)) $
                         DoA "newm" (Binop Update (Vpair ((Var "envKey" 8), (Var "newEnv" 6))) (Var "m'" 1)) Tmem $
                         App (Var "k'" 1) (Var "newm" 0))
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "m" Tmem $
        DoA "pk" (Return (Vpair (Var "p" 2, Var "k" 1))) (Tpair Any Any) $
        App (Var "f" 4) (Var "pk" 0)
  )

-- | Typed example computation using reader
-- asks for the reader value and alters it locally
cReaderT :: Comp
cReaderT = DoA "x1" (opT "ask" Vunit (Tlist Tint)) (Tlist Tint) $
          DoA "x2" ((scT "local" (LamA "x" (Tlist Tint) (Binop Append (Var "x" 0) (Vlist [Vint 5])))) "_" Tunit (opT "ask" Vunit (Tlist Tint)) (Tlist Tint)) (Tlist Tint) $
          DoA "x3" (opT "ask" Vunit (Tlist Tint)) (Tlist Tint) $ 
          Return (Vpair ((Vpair (Var "x3" 0, Var "x2" 1)), (Var "x1" 2)))

-- | Typed reader example
handle_cReaderT :: Comp
handle_cReaderT = DoA "m" (Unop Newmem Vunit) Tmem $
                  DoA "m'" (Binop Update (Vpair (Vstr "readerEnv", Vlist [Vint 1, Vint 2, Vint 3, Vint 4])) (Var "m" 0)) Tmem $
                   DoA "c" (HandleA (UFunction (UFirst UNone)) hReaderT cReaderT) (Tfunction Tmem (Tpair (Tpair (Tpair (Tlist Tint) (Tlist Tint)) (Tlist Tint)) Tmem)) $
                   DoA "x" (App (Var "c" 0) (Var "m'" 1)) (Tpair (Tpair (Tpair (Tlist Tint) (Tlist Tint)) (Tlist Tint)) Tmem) $
                   Unop Fst (Var "x" 0)

-- | Typed reader typechecking example
tReaderGam = Map.empty
tReaderSig = Map.fromList([
  ("ask", Lop "ask" Tunit (Tfunction Tmem (Tlist Tint))),
  ("local", Lsc "local" (Tfunction (Tlist Tint) (Tlist Tint)) (Tlist Tint))
  ])

tReader = checkFile tReaderGam tReaderSig handle_cReaderT (Tpair (Tpair (Tlist Tint) (Tlist Tint)) (Tlist Tint))

