module Parser where

import Syntax
import Evaluation
import Shared
import Cut
import qualified Data.Map as Map
import Prelude hiding ((<>))
import Typing

----------------------------------------------------------------
-- Parser effect (Untyped)

-- | Parser handler 
-- Consumes one token
-- token consumes one token
hToken :: Handler
hToken = Handler
  "hToken" ["token"] [] []
  ("x", Return . Lam "s" $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "token" -> Just ("x", "k", Return . Lam "s" $
      Do "b" (Binop Eq (Var "s" 0) (Vstr "")) $
      If (Var "b" 0) failure
                     ( Do "x'" (Unop HeadS (Var "s" 1)) $
                       Do "xs" (Unop TailS (Var "s" 2)) $
                       Do "b" (Binop Eq (Var "x" 5) (Var "x'" 1)) $
                       If (Var "b" 0) (app2 (Var "k" 5) (Var "x" 6) (Var "xs" 1)) failure))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
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

-- -- Parser "OR" operator
-- (<>) :: Comp -> Comp -> Comp
-- x <> y = Op "choose" Vunit ("b" :. If (Var "b" 0) (shiftC 1 x) (shiftC 1 y))

-- | Digit parser
-- digit parses a single digit
digit :: Value
digit =  Lam "_" $ 
         op "token" (Vchar '0')
      <> op "token" (Vchar '1')
      <> op "token" (Vchar '2')
      <> op "token" (Vchar '3')
      <> op "token" (Vchar '4')
      <> op "token" (Vchar '5')
      <> op "token" (Vchar '6')
      <> op "token" (Vchar '7')
      <> op "token" (Vchar '8')
      <> op "token" (Vchar '9')

-- | Many token parser
-- many1 parses one or more tokens of the given parser
many1 :: Value -> Comp
many1 p = Do "a" (App p Vunit) $
          Do "as" (many1 p <> Return (Vstr "")) $
          Do "x" (Binop ConsS (Var "a" 1) (Var "as" 0)) $
          Return (Var "x" 0)

-- | Expression parser
-- expr parses an expression
-- Doesn't use cut to abort early in case of success
expr :: Value
expr = Lam "_" $
       (Do "i" (App term Vunit) $
        Do "_" (op "token" (Vchar '+')) $
        Do "j" (App expr Vunit) $
        Do "x" (Binop Add (Var "i" 2) (Var "j" 0)) $
        Return (Var "x" 0))
    <> (Do "i" (App term Vunit) $ Return (Var "i" 0))

-- | Term parser
-- parses a multiplication term or a factor
term :: Value
term = Lam "_" $
       (Do "i" (App factor Vunit) $
        Do "_" (op "token" (Vchar '*')) $
        Do "j" (App term Vunit) $
        Do "x" (Binop Mul (Var "i" 2) (Var "j" 0)) $
        Return (Var "x" 0))
    <> (Do "i" (App factor Vunit) $ Return (Var "i" 0))

-- | Factor parser
-- factor parses a factor (a number or an expression in parenthesis)
factor :: Value
factor = Lam "_" $
         (Do "ds" (many1 digit) $
          Do "x" (Unop Read (Var "ds" 0)) $
          Return (Var "x" 0))
      <> (Do "_" (op "token" (Vchar '(')) $
          Do "i" (App expr Vunit) $
          Do "_" (op "token" (Vchar ')')) $
          Return (Var "i" 1))

-- | Expression parser using cut to abort early in case of success
-- significant reduction in execution steps for this example
expr1 :: Value
expr1 = Lam "_" $
        Do "i" (App term Vunit) $
        sc "call" Vunit ("_" :. ( Do "_" (op "token" (Vchar '+')) $
                                  Do "_" (op "cut" Vunit) $
                                  Do "j" (App expr1 Vunit) $
                                  Do "x" (Binop Add (Var "i" 4) (Var "j" 0)) $
                                  Return (Var "x" 0)) <> Return (Var "i" 1))

-- | Handling @expr1@:
exParse1 :: Comp
exParse1 = hCut # (Do "c" (hToken # App expr1 Vunit) $
                       App (Var "c" 0) (Vstr "(2+5)*8"))
-- >>> evalP exParse1
-- Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")]))

-- | Handling @expr@:
exParse2 :: Comp
exParse2 = hCut # (Do "c" (hToken # App expr Vunit) $
                      App (Var "c" 0) (Vstr "(2+5)*8"))
-- >>> evalP exParse2
-- Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")]))

--------------------------------------------------------------------------------------------------------------------------------
-- Typed Parser example

-- | Typed parser handler 
-- Handler consumes one token
-- token consumes one token
hTokenT :: Handler
hTokenT = Handler
  "hToken" ["token"] [] []
  ("x", Return . LamA "s" Tstr $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "token" -> Just ("x", "k", Return . LamA "s" Tstr $
      DoA "b" (Binop Eq (Var "s" 0) (Vstr "")) Tbool $
      If (Var "b" 0) failureT
                     ( DoA "x'" (Unop HeadS (Var "s" 1)) Tchar $
                       DoA "xs" (Unop TailS (Var "s" 2)) Tstr $
                       DoA "b" (Binop Eq (Var "x" 5) (Var "x'" 1)) Tbool $
                       If (Var "b" 0) (app2T (Var "k" 5) (Var "x" 6) (Var "xs" 1)) failureT))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  (\ forlabel -> case forlabel of
    _ -> Nothing)
  ("f", "p", "k", Return . LamA "s" Tstr $ App (Var "f" 3) (Vpair
    ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tstr Any) $
                App (Var "p'" 0) (Var "s" 2)
    , LamA "zs" (Tpair Any Tstr) $ DoA "z" (Unop Fst (Var "zs" 0)) Any $
                 DoA "s'" (Unop Snd (Var "zs" 1)) Tstr $
                 DoA "k'" (App (Var "k" 4) (Var "z" 1)) (Tfunction Tstr Any) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- | Parsing "OR" operator
(<>) :: Comp -> Comp -> Comp
x <> y = OpA "choose" Vunit (DotA "b" Tbool (If (Var "b" 0) (shiftC 1 x) (shiftC 1 y)))

-- | Digit parser
-- digit parses a single digit
digitT :: Value
digitT =  LamA "_" Tunit $ 
         opT "token" (Vchar '0') Tunit
      <> opT "token" (Vchar '1') Tunit
      <> opT "token" (Vchar '2') Tunit
      <> opT "token" (Vchar '3') Tunit
      <> opT "token" (Vchar '4') Tunit
      <> opT "token" (Vchar '5') Tunit
      <> opT "token" (Vchar '6') Tunit
      <> opT "token" (Vchar '7') Tunit
      <> opT "token" (Vchar '8') Tunit
      <> opT "token" (Vchar '9') Tunit

-- | Many token parser
-- many1 parses one or more tokens of the given parser
many1T :: Value -> Comp
many1T p = DoA "a" (App p Vunit) Tstr $
          DoA "as" (many1T p <> Return (Vstr "")) Tstr $
          DoA "x" (Binop ConsS (Var "a" 1) (Var "as" 0)) Tstr $
          Return (Var "x" 0)

-- | Expression parser
-- expr parses an expression
-- Doesn't use cut to abort early in case of success
exprT :: Value
exprT = LamA "_" Tunit $
       (DoA "i" (App termT Vunit) Tint $
        DoA "_" (opT "token" (Vchar '+') Tunit) Tunit $
        DoA "j" (App exprT Vunit) Tint $
        DoA "x" (Binop Add (Var "i" 2) (Var "j" 0)) Tint $
        Return (Var "x" 0))
    <> (DoA "i" (App termT Vunit) Tint $ Return (Var "i" 0))

-- Term parser
-- term parses a multiplication term or a factor
termT :: Value
termT = LamA "_" Tunit $
       (DoA "i" (App factorT Vunit) Tint $
        DoA "_" (opT "token" (Vchar '*') Tunit) Tunit $
        DoA "j" (App termT Vunit) Tint $
        DoA "x" (Binop Mul (Var "i" 2) (Var "j" 0)) Tint $
        Return (Var "x" 0))
    <> (DoA "i" (App factorT Vunit) Tint $ Return (Var "i" 0))

-- | Factor Parser
-- factor parses a factor (a number or an expression in parenthesis)
factorT :: Value
factorT = LamA "_" Tunit $
         (DoA "ds" (many1T digitT) Tstr $
          DoA "x" (Unop Read (Var "ds" 0)) Tint $
          Return (Var "x" 0))
      <> (DoA "_" (opT "token" (Vchar '(') Tunit) Tunit $
          DoA "i" (App exprT Vunit) Tint $
          DoA "_" (opT "token" (Vchar ')') Tunit) Tunit $
          Return (Var "i" 1))

-- | Expression parser
-- Uses cut to abort early in case of success
expr1T :: Value
expr1T = LamA "_" Tunit $
        DoA "i" (App termT Vunit) Tint $
        ScA "call" Vunit (DotA "_" Tunit ((DoA "_" (opT "token" (Vchar '+') Tunit) Tunit $ 
                                            DoA "_" (opT "cut" Vunit Tunit) Tunit $ 
                                            DoA "j" (App expr1T Vunit) Tint $ 
                                            DoA "x" (Binop Add (Var "i" 4) (Var "j" 0)) Tint $ 
                                            Return (Var "x" 0)) <> Return (Var "i" 1))) 
                          (DotA "z" Any (Return (Var "z" 0)))

-- | Typed parser example to parse and compute calculation from string
-- Uses early abort with cut
handle_expr1T :: Comp
handle_expr1T = HandleA (URet (UList UNone)) hCutT (DoA "c" (HandleA (UFunction (UFirst UNone)) hTokenT (App expr1T Vunit)) (Tfunction Tstr Any) $
                       App (Var "c" 0) (Vstr "(2+5)*8"))

-- | Typed parser example to parse and compute calculation from string 
handle_exprT :: Comp
handle_exprT = HandleA (URet (UList UNone)) hCutT (DoA "c" (HandleA (UFunction (UFirst UNone)) hTokenT (App exprT Vunit)) (Tfunction Tstr Any) $
                      App (Var "c" 0) (Vstr "(2+5)*8"))

-- | First typed parser typechecking example
tParseGam = Map.fromList([
  ("tCutA", (Tpair Tint Tstr))])
tParseSig = Map.fromList([
  ("token", Lop "token" (Tpair Tstr Any) (Tfunction Tchar Any)),
  ("cut", Lop "cut" Tunit (Tfunction Tunit Any)),
  ("call", Lsc "call" Tunit (Tfunction Tunit Any)),
  ("choose", Lop "choose" Tunit Tbool),
  ("fail", Lop "fail" Tunit Tunit)
  ])

tParse1 = checkFile tParseGam tParseSig handle_expr1T (Tret (Tlist (Tpair Tint Tstr))) 
tParse2 = checkFile tParseGam tParseSig handle_exprT (Tret (Tlist (Tpair Tint Tstr))) 
