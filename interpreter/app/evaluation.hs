module Evaluation where

import Syntax
import Data.List
import System.Random

type Step = String

-- | Evaluation
eval :: Comp ->  [Comp]
eval c = case eval1 c of
  Just c' -> c:(eval c')
  Nothing -> [c]

-- | Evaluation for parser (due to recursive defintions we can not evaluate/show intermediate steps)
evalP :: Comp ->  Comp
evalP c = case eval1 c of
  Just c' -> evalP c'
  Nothing -> c

-- | Evaluation with steps
evalFile :: Comp -> IO ()
evalFile c = do
  let steps = eval' c
  writeFile "reduction" (prettyprint steps 1)

-- | Evaluation without steps
evalFile' :: Comp -> IO ()
evalFile' c = do
  let steps = eval c
  writeFile "reductionNoSteps" (prettyprint' steps 1)

-- | Verbose evaluation
eval' :: Comp -> [(Step, Comp)]
eval' c = case eval1' c of
  (step , Just c') -> (step, c) : eval' c'
  (step , Nothing) -> [(step, c)]

-- | Pretty print verbose evaluation
prettyprint :: [(Step, Comp)] -> Int -> String
prettyprint [] _ = "" 
prettyprint ((step, c) : cs) nr = show c ++ "\n\n" ++ show nr ++ ".\n{-- " ++ step ++ " --}" ++ "\n\n" ++ prettyprint cs (nr+1)

-- | Pretty print verbose evaluation
prettyprint' :: [Comp] -> Int -> String
prettyprint' [] _ = "" 
prettyprint' (c : cs) nr = show c ++ "\n\n" ++ show nr ++ ".\n" ++ prettyprint' cs (nr+1)

-- | Single step evaluation
eval1 :: Comp -> Maybe Comp
eval1 (App (Lam x c) v) = return . shiftC (-1) $ subst c [(shiftV 1 v, 0)] -- E-AppAbs

eval1 (Let x v c) = return . shiftC (-1) $ subst c [(shiftV 1 v, 0)] -- E-Let
eval1 (Letrec x v c) = return . shiftC (-1) $ subst c [(shiftV 1 (Vrec x v v), 0)] -- E-LetRec
eval1 (App (Vrec x v1 v2) v) = return . shiftC (-1) $ subst (App v2 v) [(shiftV 1 (Vrec x v1 v2), 0)] -- E-AppRec

eval1 (Do x (Return v) c) = return . shiftC (-1) $ subst c [(shiftV 1 v, 0)] -- E-DoRet
eval1 (Do x (Op l v (y :. c1)) c2) = return $ Op l v (y :. Do x c1 c2) -- E-DoOp
eval1 (Do x (Sc l v (y :. c1) (z :. c2)) c3) = return $ Sc l v (y :. c1) (z :. Do x c2 c3) -- E-DoSc
eval1 (Do x (For l v (y :. c1) (z :. c2)) c3) = return $ For l v (y :. c1) (z :. Do x c2 c3) -- E-DoFor
eval1 (Do x c1 c2) = do c1' <- eval1 c1; return $ Do x c1' c2 -- E-Do

eval1 (Handle (Parallel (x, p, k, c) r fwd) (For l v (y :. c1) (z :. c2))) = Just (shiftC (-3) $ subst c [(shiftV 3 v, 2), -- E-Traverse
                         (shiftV 3 $ Lam y (Handle (Parallel (x, p, k, c) r fwd) c1), 1),
                         (shiftV 3 $ Lam z (Handle (Parallel (x, p, k, c) r fwd) c2), 0)])

eval1 (Handle h (Return v)) = return $ let (x, cr) = hreturn h in -- E-HandRet
  shiftC (-1) $ subst cr [(shiftV 1 v, 0)]
eval1 (Handle h (Op l v (y :. c1))) = return $ case hop h l of -- E-HandOp
  Just (x, k, c) -> shiftC (-2) $ subst c [ (shiftV 2 v, 1)
                                          , (shiftV 2 $ Lam y (Handle h c1), 0) ]
  Nothing -> Op l v (y :. Handle h c1) -- E-FwdOp
eval1 (Handle h (Sc l v (y :. c1) (z :. c2))) = return $ case hsc h l of -- E-HandSc
  Just (x, p, k, c) -> shiftC (-3) $ subst c [ (shiftV 3 v, 2)
                                             , (shiftV 3 $ Lam y (Handle h c1), 1)
                                             , (shiftV 3 $ Lam z (Handle h c2), 0) ]
  Nothing -> case hfwd h of -- E-FwdSc
    (f, p, k, c) -> shiftC (-3) $ subst c
      [ (shiftV 3 $ Lam y (Handle h c1), 1)
      , (shiftV 3 $ Lam z (Handle h c2), 0)
      , (Lam "pk" $ 
          Do "p" (Unop Fst (Var "pk" 0)) $
          Do "k" (Unop Snd (Var "pk" 1)) $
          Sc l (shiftV 3 v) (y :. App (Var p 2) (Var y 0)) (z :. App (Var k 1) (Var z 0)), 2)
      ]
eval1 (Handle h (For label v (y :. c1) (z :. c2))) = return $ case hfor h label of -- E-HandFor
    Just (x, l, k, c) -> shiftC (-3) $ subst c [ (shiftV 3 v, 2)
                                                 , (shiftV 3 $ Lam l (For label (Var l 0) (y :. Handle h c1) (z :. Return (Var z 0))), 1)
                                                 , (shiftV 3 $ Lam z (Handle h c2), 0) ]
    Nothing -> case hfwd h of -- E-FwdSc
      (f, p, k, c) -> shiftC (-3) $ subst c
        [ (shiftV 3 $ Lam y (Handle h c1), 1)
        , (shiftV 3 $ Lam z (Handle h c2), 0)
        , (Lam "pk" $ 
            Do "p" (Unop Fst (Var "pk" 0)) $
            Do "k" (Unop Snd (Var "pk" 1)) $
            For label (shiftV 3 v) (y :. App (Var p 2) (Var y 0)) (z :. App (Var k 1) (Var z 0)), 2)
        ]
eval1 (Handle h c) = do c' <- eval1 c; return $ Handle h c' -- E-Hand 
eval1 (If (Vbool True) c1 c2) = return c1 -- E-IfTrue
eval1 (If (Vbool False) c1 c2) = return c2 -- E-IfFalse
eval1 (Unop op v) = evalUnop op v -- E-Unop
eval1 (Binop op v1 v2) = evalBinop op v1 v2 -- E-Binop

eval1 (Case (Vsum v) x c1 y c2) = return $ case v of
  Left t  -> shiftC (-1) $ subst c1 [(shiftV 1 t, 0)]
  Right t -> shiftC (-1) $ subst c2 [(shiftV 1 t, 0)]

eval1 c = Nothing

evalUnop :: Op1 -> Value -> Maybe Comp
evalUnop Fst (Vpair (v1, v2)) = return $ Return v1
evalUnop Snd (Vpair (v1, v2)) = return $ Return v2
evalUnop Head (Vlist (x:_)) = return $ Return x
evalUnop HeadS (Vstr xs) = return . Return . Vchar . head $ xs
evalUnop Tail (Vlist (_:xs)) = return $ Return $ Vlist xs
evalUnop TailS (Vstr xs) = return . Return . Vstr . tail $ xs
evalUnop Empty (Vlist []) = return . Return . Vbool $ True
evalUnop Empty _ = return . Return . Vbool $ False
evalUnop Read (Vstr xs) = return . Return . Vint $ read xs
evalUnop Close (Vret (Vlist xs))  = return . Return . Vflag . Vlist $ xs
evalUnop Close (Vflag (Vlist xs)) = return . Return . Vflag . Vlist $ xs
evalUnop Open  (Vret (Vlist xs))  = return . Return . Vret . Vlist $ xs
evalUnop Open  (Vflag (Vlist xs)) = return . Return . Vret . Vlist $ xs
evalUnop Newmem Vunit = return . Return $ Vmem emptymem
evalUnop FirstFail (Vlist lst) = return $ case sequence (map firstError lst) of
    Left e  -> Return $ Vsum (Left e)
    Right x -> Return $ Vsum (Right $ Vlist (fmap (\(Vsum (Right x)) -> x) lst))
  where firstError x = case x of Vsum (Left e)  -> Left e
                                 Vsum (Right x) -> Right x
                                 e              -> error ("firstError: not a sum: " ++ show e)
evalUnop CartesianProd (Vlist lst) = 
  let list = map (\l -> Vlist l) (subsequences lst) in
    return . Return . Vlist $ list
evalUnop Rand (Vkey g) = let (val, key) = randomR (0, 100) g in
  return . Return . Vpair $ (Vint val, Vkey key)
evalUnop SplitKeyPair (Vkey g) = let (key1, key2) = split g in
  return . Return . Vpair $ (Vkey key1, Vkey key2)

evalBinop :: Op2 -> Value -> Value -> Maybe Comp
evalBinop Add (Vint x) (Vint y) = return . Return . Vint $ x + y
evalBinop Minus (Vint x) (Vint y) = return . Return . Vint $ x - y
evalBinop Min (Vint x) (Vint y) = return . Return . Vint $ min x y
evalBinop Mul (Vint x) (Vint y) = return . Return . Vint $ x * y
evalBinop ConcatMap (Vlist xs) f = return $ case xs of
  [] -> Return . Vlist $ []
  (x:xs) -> Do "as" (App f x) $
            Do "as'" (Binop ConcatMap (shiftV 1 $ Vlist xs) (shiftV 1 f)) $
            Binop Append (Var "as" 1) (Var "as'" 0)
evalBinop ConcatMapCutList (Vret (Vlist xs)) f = return $ case xs of
  [] -> Return . Vret . Vlist $ []
  (x:xs) -> Do "as" (App f x) $
            Do "as'" (Binop ConcatMapCutList (shiftV 1 $ Vret (Vlist xs)) (shiftV 1 f)) $
            Binop AppendCut (Var "as" 1) (Var "as'" 0)
evalBinop ConcatMapCutList (Vflag (Vlist xs)) f = return $ case xs of
  [] -> Return . Vflag . Vlist $ []
  (x:xs) -> Do "as" (App f x) $
            Do "as'" (Binop ConcatMapCutList (shiftV 1 $ Vflag (Vlist xs)) (shiftV 1 f)) $
            Binop AppendCut (Var "as" 1) (Var "as'" 0)
evalBinop AppendCut (Vret (Vlist xs)) (Vret (Vlist ys))  = return . Return . Vret  . Vlist $ xs ++ ys
evalBinop AppendCut (Vret (Vlist xs)) (Vflag (Vlist ys)) = return . Return . Vflag . Vlist $ xs ++ ys
evalBinop AppendCut (Vflag (Vlist xs)) _                 = return . Return . Vflag . Vlist $ xs
evalBinop Append (Vlist xs) (Vlist ys) = return . Return . Vlist $ xs ++ ys
evalBinop Append x (Vlist xs) = return . Return . Vlist $ (x:xs)
evalBinop AppendS (Vstr xs) (Vstr ys) = return . Return . Vstr $ (xs ++ ys)
evalBinop ConsS (Vchar x) (Vstr xs) = return . Return . Vstr $ (x:xs)
evalBinop Larger (Vint x) (Vint y) = return $ if x > y then Return (Vbool True) else Return (Vbool False)
evalBinop Eq v1 v2 = return $ if v1 == v2 then Return (Vbool True) else Return (Vbool False)
evalBinop Retrieve (Vstr name) (Vmem m) = return . Return $ retrieve name m
evalBinop Update (Vpair (Vstr x, v)) (Vmem m) = return . Return $ Vmem (update (x, v) m)
evalBinop Map (Vlist xs) f = return $ case xs of
  [] -> Return . Vlist $ [] -- E-MapNil
  (x:xs) -> Do "y" (App f x) $ -- E-Map
            Do "ys'" (Binop Map (shiftV 1 $ Vlist xs) (shiftV 1 f)) $
            Binop Append (Vlist [Var "y" 1]) (Var "ys" 0)
evalBinop SplitKey (Vkey g) (Vlist list) = let n = length list in
  return . Return $ Vlist $ map (\x -> Vkey x) (splitTo g n) where
    splitTo g 0 = []
    splitTo g 1 = [g]
    splitTo g n = let (g1, g2) = split g in g1 : splitTo g2 (n-1)
evalBinop Zip (Vlist xs) (Vlist ys) =  return $ case xs of
  [] -> Return . Vlist $ []
  (x:xs) -> case ys of
    [] -> Return . Vlist $ []
    (y:ys) -> Do "z" (App x y) $
              Do "zs" (Binop Zip (shiftV 1 $ Vlist xs) (shiftV 1 $ Vlist ys)) $
              Binop Append (Vlist [Var "z" 1]) (Var "zs" 0)
evalBinop _ _ _ = Nothing

-- | Single step evaluation with chosen reduction step
eval1' :: Comp -> (Step, Maybe Comp)
eval1' (App (Lam x c) v) = ("E-AppAbs", return . shiftC (-1) $ subst c [(shiftV 1 v, 0)])-- E-AppAbs
eval1' (Let x v c) = ("E-Let", return . shiftC (-1) $ subst c [(shiftV 1 v, 0)]) -- E-Let
eval1' (Letrec x v c) = ("E-LetRec", return . shiftC (-1) $ subst c [(shiftV 1 (Vrec x v v), 0)]) -- E-LetRec
eval1' (App (Vrec x v1 v2) v) = ("E-AppRec", return . shiftC (-1) $ subst (App v2 v) [(shiftV 1 (Vrec x v1 v2), 0)]) -- E-AppRec

eval1' (Do x (Return v) c) = ("E-DoRet", return . shiftC (-1) $ subst c [(shiftV 1 v, 0)]) -- E-DoRet
eval1' (Do x (Op l v (y :. c1)) c2) = ("E-DoOp", return $ Op l v (y :. Do x c1 c2)) -- E-DoOp
eval1' (Do x (Sc l v (y :. c1) (z :. c2)) c3) = ("E-DoSc", return $ Sc l v (y :. c1) (z :. Do x c2 c3)) -- E-DoSc
eval1' (Do x (For l v (y :. c1) (z :. c2)) c3) = ("E-DoFor", return $ For l v (y :. c1) (z :. Do x c2 c3)) -- E-DoFor
eval1' (Do x c1 c2) = case (eval1' c1) of 
    (step, (Just c1')) -> ("E-Do and " ++ step, return $ Do x c1' c2) -- E-Do
    (step, Nothing) -> ("Nothing", Nothing)

eval1' (Handle (Parallel (x, p, k, c) r fwd) (For l v (y :. c1) (z :. c2))) = ("E-Traverse" , Just (shiftC (-3) $ subst c [(shiftV 3 v, 2), -- E-Traverse
                         (shiftV 3 $ Lam y (Handle (Parallel (x, p, k, c) r fwd) c1), 1),
                         (shiftV 3 $ Lam z (Handle (Parallel (x, p, k, c) r fwd) c2), 0)]))

eval1' (Handle h (Return v)) = ("E-HandRet",  return $ let (x, cr) = hreturn h in -- E-HandRet
  shiftC (-1) $ subst cr [(shiftV 1 v, 0)])
eval1' (Handle h (Op l v (y :. c1))) = case hop h l of -- E-HandOp
  Just (x, k, c) -> ("E-HandOp", return $ shiftC (-2) $ subst c [ (shiftV 2 v, 1)
                                          , (shiftV 2 $ Lam y (Handle h c1), 0) ])
  Nothing -> ("E-FwdOp", return $ Op l v (y :. Handle h c1)) -- E-FwdOp
eval1' (Handle h (Sc l v (y :. c1) (z :. c2))) = case hsc h l of -- E-HandSc
  Just (x, p, k, c) -> ("E-HandSc", return $ shiftC (-3) $ subst c [ (shiftV 3 v, 2)
                                             , (shiftV 3 $ Lam y (Handle h c1), 1)
                                             , (shiftV 3 $ Lam z (Handle h c2), 0) ])
  Nothing -> case hfwd h of -- E-FwdSc
    (f, p, k, c) -> ("E-FwdSc", return $ shiftC (-3) $ subst c
      [ (shiftV 3 $ Lam y (Handle h c1), 1)
      , (shiftV 3 $ Lam z (Handle h c2), 0)
      , (Lam "pk" $ 
          Do "p" (Unop Fst (Var "pk" 0)) $
          Do "k" (Unop Snd (Var "pk" 1)) $
          Sc l (shiftV 3 v) (y :. App (Var p 2) (Var y 0)) (z :. App (Var k 1) (Var z 0)), 2)
      ])
eval1' (Handle h (For label v (y :. c1) (z :. c2))) = case hfor h label of -- E-HandFor
    Just (x, l, k, c) -> ("E-HandFor", return $ shiftC (-3) $ subst c [ (shiftV 3 v, 2)
                                                 , (shiftV 3 $ Lam l (For label (Var l 0) (y :. Handle h c1) (z :.Return (Var z 0))), 1)
                                                 , (shiftV 3 $ Lam z (Handle h c2), 0) ])
    Nothing -> ("E-FwdFor", return $ case hfwd h of -- E-FwdSc
      (f, p, k, c) -> shiftC (-3) $ subst c
        [ (shiftV 3 $ Lam y (Handle h c1), 1)
        , (shiftV 3 $ Lam z (Handle h c2), 0)
        , (Lam "pk" $ 
            Do "p" (Unop Fst (Var "pk" 0)) $
            Do "k" (Unop Snd (Var "pk" 1)) $
            For label (shiftV 3 v) (y :. App (Var p 2) (Var y 0)) (z :. App (Var k 1) (Var z 0)), 2)
        ]) -- E-FwdFor
eval1' (Handle h c) = case eval1' c of 
    (step, (Just c')) -> ("E-Hand and " ++ step, return $ Handle h c') -- E-Hand
    (step, Nothing) -> ("Nothing", Nothing)

eval1' (If (Vbool True) c1 c2) = ("E-IfTrue", return c1) -- E-IfTrue
eval1' (If (Vbool False) c1 c2) = ("E-IfTrue", return c2) -- E-IfFalse
eval1' (Unop op v) = case evalUnop op v of -- E-Unop
    Just c -> ("E-Unop", return $ c)
    Nothing -> ("Nothing", Nothing)
eval1' (Binop op v1 v2) = case evalBinop op v1 v2 of -- E-Binop
    Just c -> ("E-Binop", return $ c)
    Nothing -> ("Nothing", Nothing)

eval1' (Case (Vsum v) x c1 y c2) = case v of
  Left t  -> ("E-CaseLeft", return $ shiftC (-1) $ subst c1 [(shiftV 1 t, 0)]) -- E-CaseLeft
  Right t -> ("E-CaseRight", return $ shiftC (-1) $ subst c2 [(shiftV 1 t, 0)]) -- E-CaseRight

eval1' c = ("Nothing", Nothing)

----------------------------------------------------------------

-- | The @lift@ syntactic sugar
lift2fwd :: (Name, Name, Comp) -> (Name, Name, Name, Comp)
lift2fwd (k, z, c) = ( "f", "p", "k",
  App (Var "f" 2) $ Vpair (Var "p" 1, Lam "z" c ))

----------------------------------------------------------------
-- Auxiliary functions for implementing the evaluation:

mapC :: (Comp -> Comp) -> (Value -> Value) -> (Comp -> Comp)
mapC fc fv c = case c of
  Return v -> Return (fv v)
  Op l v (y :. c) -> Op l (fv v) (y :. fc c)
  Sc l v (y :. c1) (z :. c2) -> Sc l (fv v) (y :. fc c1) (z :. fc c2)
  For l v (y :. c1) (z :. c2) -> For l (fv v) (y :. fc c1) (z :. fc c2)
  Handle h c -> Handle (mapH fc h) (fc c)
  Do x c1 c2 -> Do x (fc c1) (fc c2)
  App v1 v2 -> App (fv v1) (fv v2)
  Let x v c  -> Let x (fv v) (fc c)
  Letrec x v c -> Letrec x (fv v) (fc c)
  If v c1 c2 -> If (fv v) (fc c1) (fc c2)
  Binop op v1 v2 -> Binop op (fv v1) (fv v2)
  Unop op v -> Unop op (fv v)
  Case v x c1 y c2 -> Case (fv v) x (fc c1) y (fc c2)
  Undefined -> Undefined
  -- oth -> oth

mapH :: (Comp -> Comp) -> Handler -> Handler
mapH fc h = h { hreturn = hr, hop = ho, hsc = hs, hfwd = hf }
  where
    hr = let (x, c) = hreturn h in (x, fc c)
    ho l = hop h l >>= \ (x, k, c) -> return (x, k, fc c)
    hs l = hsc h l >>= \ (x, p, k, c) -> return (x, p, k, fc c)
    hf = let (f, p, k, c) = hfwd h in (f, p, k, fc c)

mapV :: (Comp -> Comp) -> (Value -> Value) -> Value -> Value
mapV fc fv v = case v of
  Var x n -> Var x n
  Lam x c -> Lam x (fc c)
  Vpair (v1, v2) -> Vpair (fv v1, fv v2)
  Vsum v -> case v of
    Left t -> Vsum (Left (fv t))
    Right t -> Vsum (Right (fv t))
  Vlist xs -> Vlist (fmap fv xs)
  Vmem m -> Vmem (fmap fv m)
  Vret v -> Vret (fv v)
  Vflag v -> Vflag (fv v)
  Vunit -> Vunit
  Vbool b -> Vbool b
  Vint n -> Vint n
  Vstr s -> Vstr s
  Vchar c -> Vchar c
  Vrec x v1 v2 -> Vrec x (fv v1) (fv v2)
  Vkey v -> Vkey v
  -- oth -> oth

varmapC :: (Int -> (Name, Int) -> Value) -> Int -> Comp -> Comp
varmapC onvar cur c = case c of
    Op l v (y :. c) -> Op l (fv cur v) (y :. fc (cur+1) c)
    Sc l v (y :. c1) (z :. c2) -> Sc l (fv cur v) (y :. fc (cur+1) c1) (z :. fc (cur+1) c2)
    For l v (y :. c1) (z :. c2) -> For l (fv cur v) (y :. fc (cur+1) c1) (z :. fc (cur+1) c2)
    Handle h c -> Handle (varmapH onvar cur h) (fc cur c)
    Do x c1 c2 -> Do x (fc cur c1) (fc (cur+1) c2)
    Let x v c  -> Let x (fv cur v) (fc (cur+1) c)
    Letrec x v c -> Letrec x (fv (cur+1) v) (fc (cur+1) c)
    Case v x c1 y c2 -> Case (fv cur v) x (fc (cur+1) c1) y (fc (cur+1) c2)
    oth -> mapC (fc cur) (fv cur) oth
  where
    fc = varmapC onvar
    fv = varmapV onvar

varmapH :: (Int -> (Name, Int) -> Value) -> Int -> Handler -> Handler
varmapH onvar cur (Parallel h1 h2 h3) = (Parallel h1' h2' h3') -- parallel handlers 
  where
    h1' = let (x, l, k, c) = h1 in (x, l, k, fc (cur+3) c)
    h2' = let (x, c) = h2 in (x, fc (cur+1) c)
    h3' = let (f, p, k, c) = h3 in (f, p, k, fc (cur+4) c)
    fc = varmapC onvar
varmapH onvar cur h = h { hreturn = hr, hop = ho, hsc = hs, hfwd = hf } -- sequential handlers
  where
    hr = let (x, c) = hreturn h in (x, fc (cur+1) c)
    ho l = hop h l >>= \ (x, k, c) -> return (x, k, fc (cur+2) c)
    hs l = hsc h l >>= \ (x, p, k, c) -> return (x, p, k, fc (cur+3) c)
    hf = let (f, p, k, c) = hfwd h in (f, p, k, fc (cur+4) c)
    fc = varmapC onvar
    fv = varmapV onvar

varmapV :: (Int -> (Name, Int) -> Value) -> Int -> Value -> Value
varmapV onvar cur v = case v of
    Var x i -> onvar cur (x, i)
    Lam x c -> Lam x (fc (cur+1) c)
    oth -> mapV (fc cur) (fv cur) oth
  where
    fc = varmapC onvar
    fv = varmapV onvar

shiftV :: Int -> Value -> Value
shiftV delta v = varmapV (\ cur (x, i) -> if i >= cur then Var x (i+delta) else Var x i) 0 v

shiftC :: Int -> Comp -> Comp
shiftC delta v = varmapC (\ cur (x, i) -> if i >= cur then Var x (i+delta) else Var x i) 0 v

substC :: Comp -> (Value, Int) -> Comp
substC c (v, j) = varmapC (\ cur (x, i) -> if i == j+cur then shiftV cur v else Var x i) 0 c

subst :: Comp -> [(Value, Int)] -> Comp
subst c [] = c
subst c ((v, j) : as) = subst (substC c (v, j)) as