module Weak where

import Syntax
import Evaluation
import Accum
import Shared
import qualified Data.Map as Map
import Typing

----------------------------------------------------------------
-- Weak exceptions example

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

--------------------------------------------------------------------------------------------------------------------------------
-- Weak exceptions example as scoped effect

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

-------------------------------------------------------------------------------
-- Typed weak exceptions example

-- Typed weak exceptions handler
-- Implements exceptions as a parallel effect
-- If a computation running in parallel with other computation encounters an exception
-- Other computation don't immediately stop computation
-- But they do not run their continuation
hWeakT :: Handler
hWeakT = Handler
  "hWeak" ["throw"] [] ["for"]
  ("x", Return (Vsum (Right (Var "x" 0))))
  (\ oplabel -> case oplabel of
    "throw" -> Just ("x", "k", Return (Vsum (Left (Var "x" 1))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    "for" -> (Just ("list", "l", "k",
          DoA "results" (App (Var "l" 1) (Var "list" 2)) (Tlist (Tsum Tstr Tunit)) $ 
          DoA "FirstFail" (Unop FirstFail (Var "results" 0)) (Tsum Tstr Tunit) $
          Case (Var "FirstFail" 0) 
            "error" (Return $ Vsum $ Left (Var "error" 0))
            "t" (App (Var "k" 3) (Var "t" 0))
        ))
    _ -> Nothing)
  ("f", "p", "k", 
      DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
      App (Var "f" 3) (Var "pk" 0)
  )

-- Typed weak exceptions example computation
cWeakT :: Comp
cWeakT = DoA "_" (OpA "accum" (Vstr "start ") (DotA "y" Tunit (Return (Var "y" 0)))) Tunit $ 
         (ForA "for" (Vlist [Vstr "1", Vstr "2", Vstr "3", Vstr "4", Vstr "5"])
         (DotA "y" Tstr (Do "eq2" (Binop Eq (Var "y" 0) (Vstr "2")) $
         If (Var "eq2" 0)   (DoA "_" (OpA "accum" (Vstr "!") (DotA "y" Tunit (Return (Var "y" 0)))) Tunit $
                            DoA "_" (OpA "throw" (Vstr "error") (DotA "y" Tunit (Return (Var "y" 0)))) Tunit $
                            OpA "accum" (Vstr "unreachable") (DotA "y" Tunit (Return (Var "y" 0))))
        (OpA "accum" (Var "y" 1) (DotA "y" Tunit (Return (Var "y" 0))))))
        (DotA "z" Any (Return (Var "z" 0))))

-- Typed weak exceptions 
tWeakGam = Map.empty
tWeakSig = Map.fromList([
  ("accum", Lop "accum" Tstr (Tpair Tstr Tunit)),
  ("throw", Lop "throw" Tstr (Tpair Tstr Tunit)),
  ("for", Lfor "for" Any)
  ])
tWeakComp1 = HandleA UNone hPureT (HandleA (USecond UNone) hAccumST (HandleA (USum UNone UNone) hWeakT cWeakT))
tWeak1 = checkFile tWeakGam tWeakSig tWeakComp1 (Tpair Tstr (Tsum Tstr Tunit))

-- Typed weak exceptions handler as scoped effect
-- Implements exceptions as a parallel effect
-- If a computation running in parallel with other computation encounters an exception
-- Other computation don't immediately stop computation
-- But they do not run their continuation
hWeakScT :: Handler
hWeakScT = Handler
  "hWeak" ["throw"] ["for"] []
  ("x", Return (Vsum (Right (Var "x" 0))))
  (\ oplabel -> case oplabel of
    "throw" -> Just ("x", "k", Return (Vsum (Left (Var "x" 1))))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "for" -> Just ("x", "p", "k",
      DoA "results" (ScA "for" (Var "x" 2) (DotA "y" Any (App (Var "p" 2) (Var "y" 0))) (DotA "z" Any (Return (Var "z" 0)))) Any $ 
      DoA "FirstFail" (Unop FirstFail (Var "results" 0)) (Tsum Tstr Tunit) $
      Case (Var "FirstFail" 0) 
        "error" (Return $ Vsum $ Left (Var "error" 0))
        "t" (App (Var "k" 3) (Var "t" 0)))
    _ -> Nothing)
  (\ forlabel -> case forlabel of 
    _ -> Nothing)
  ("f", "p", "k", 
        DoA "pk" (Return (Vpair (Var "p" 1, Var "k" 0))) (Tpair Any Any) $
        App (Var "f" 3) (Var "pk" 0)
  )

-- Typed weak exceptions as scoped effect example computation
cWeakScT :: Comp
cWeakScT = DoA "_" (OpA "accum" (Vstr "start ") (DotA "y" Any (Return (Var "y" 0)))) Any $ 
         (ScA "for" (Vlist [Vstr "1", Vstr "2", Vstr "3", Vstr "4", Vstr "5"])
         (DotA "y" Tstr (Do "eq2" (Binop Eq (Var "y" 0) (Vstr "2")) $
         If (Var "eq2" 0)   (DoA "_" (OpA "accum" (Vstr "!") (DotA "y" Any (Return (Var "y" 0)))) Any $
                            DoA "_" (OpA "throw" (Vstr "error") (DotA "y" Any (Return (Var "y" 0)))) Any $
                            OpA "accum" (Vstr "unreachable") (DotA "y" Any (Return (Var "y" 0))))
        (OpA "accum" (Var "y" 1) (DotA "y" Any (Return (Var "y" 0))))))
        (DotA "z" Any (Return (Var "z" 0))))

-- Typed weak exceptions as scoped effect example
tWeakSigSc = Map.fromList([
  ("accum", Lop "accum" Tstr (Tpair Tstr Tunit)),
  ("throw", Lop "throw" Tstr (Tpair Tstr Tunit)),
  ("for", Lsc "for" Any Any)
  ])

tWeakComp2 = HandleA UNone hPureScT (HandleA (USecond UNone) hAccumSScT (HandleA (USum UNone UNone) hWeakScT cWeakScT))
tWeak2 = checkFile tWeakGam tWeakSigSc tWeakComp2 (Tpair Tstr (Tsum Tstr Tunit))

