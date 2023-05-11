module Typing where

import Syntax
import Evaluation
import Debug.Trace
import qualified Data.Map as Map
import qualified Data.Set as Set

type Gamma = Map.Map Name ValueType
type Sigma = Map.Map Name Label

typeCheckEval :: Gamma -> Sigma -> Comp -> ComputationType -> Bool -> [(String, Comp)]
typeCheckEval gam sig c ct tr = 
  if check "---- New step ----" (typeCheckC gam sig c ct tr) tr
    then case eval1' c of
      (step, Just c') -> (step, c) : typeCheckEval gam sig c' ct tr
      (step, Nothing) -> [("Nothing", c)]
  else [("No more evaluation", c)]

-- | Evaluation with steps
checkFile :: Gamma -> Sigma -> Comp -> ComputationType -> IO ()
checkFile gam sig c ct = do
  let steps = typeCheckEval gam sig c ct True
  writeFile "typecheck" (prettyprintT steps 1)

-- | Pretty print verbose evaluation
prettyprintT :: [(String, Comp)] -> Int -> String
prettyprintT [] _ = "" 
prettyprintT ((step, c):xs) n = 
  "\n Step " ++ show n ++ ": " ++ step ++ "\n" ++ show c ++ "\n" ++ prettyprintT xs (n+1) ++ "\n"


check :: String -> a -> Bool -> a
check s ch tr = 
  if tr 
    then trace s ch
    else ch   


typeCheckC :: Gamma -> Sigma -> Comp -> ComputationType -> Bool -> Bool
typeCheckC _ _ _ Any _ = True
typeCheckC _ _ Undefined _ _ = True
typeCheckC gam sig (Return v) vt tr = -- SD-Ret
  if check ("SD-Ret: Checking " ++ show v ++ " to be of type " ++ show vt) (typeCheckV gam sig v vt tr) tr
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show vt)
typeCheckC gam sig (App v1 v2) vt2 tr = case v1 of -- SD-App
  (LamA n vt1 c) -> 
    if check ("SD-App (Lam1): Checking " ++ show c ++ " to be of type " ++ show vt2) (typeCheckC (Map.insert n vt1 gam) sig c vt2 tr) tr
      then if check ("SD-App (Lam2): Checking " ++ show v2 ++ " to be of type " ++ show vt1) (typeCheckV gam sig v2 vt1 tr) tr
        then True
        else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show vt1 ++ " in " ++ show (LamA n vt1 c))
      else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show (Tfunction vt1 vt2)) 
  (Var n _) -> case Map.lookup n gam of
    Just (Tfunction vt1 vt3) -> 
      if check ("SD-App (Var): Checking " ++ show v2 ++ " to be of type " ++ show vt1) (typeCheckV gam sig v2 vt1 tr) tr
        then True
        else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show vt1)
    Just Any -> True
    Just x -> error ("Typecheck failed: " ++ show x ++ " is not a function")
    Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
  (Lam n c) -> error ("Typecheck failed: " ++ show (Lam n c) ++ " is not annotated")
  (Vrec n v1 v2) -> True -- SD-AppRec TODO
  _ -> error ("Typecheck failed: " ++ show v1 ++ " is not a function")
typeCheckC gam sig (DoA n c1 vt1 c2) vt2 tr = -- SD-Do
  if check ("SD-Do (1): Checking " ++ show c2 ++ " to be of type " ++ show vt2) (typeCheckC (Map.insert n vt1 gam) sig c2 vt2 tr) tr
    then if check ("SD-Do (2): Checking " ++ show c1 ++ " to be of type " ++ show vt1) (typeCheckC gam sig c1 vt1 tr) tr
      then True
      else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show vt1)
    else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt2)
typeCheckC gam sig (LetA n v vt1 c) vt2 tr = -- SD-Let
  if check ("SD-Let: Checking " ++ show v ++ " to be of type " ++ show vt1) (typeCheckV gam sig v vt1 tr) tr
    then if check ("SD-Let: Checking " ++ show c ++ " to be of type " ++ show vt2) (typeCheckC (Map.insert n vt1 gam) sig c vt2 tr) tr
      then True
      else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt2)
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show vt1)
typeCheckC gam sig (HandleA t h c) vt tr = -- SD-Hand 
  if check ("SD-Hand: Checking " ++ show c ++ " to be of type " ++ show vt') (typeCheckC gam sig c vt' tr) tr
    then True
    else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt')
    where 
      vt' = transformH gam t vt tr
typeCheckC gam sig (OpA n v (DotA y a c)) vt2 tr = case Map.lookup n sig of -- SD-Op
  Just (Lop _ lt1 lt2) -> 
    if check ("SD-Op: Checking: " ++ show v ++ " to be of type " ++ show lt1) (typeCheckV gam sig v lt1 tr) tr
      then if check ("SD-Op: Checking " ++ show c ++ " to be of type " ++ show vt2) (typeCheckC (Map.insert y a gam) sig c vt2 tr) tr
        then True
        else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt2)
      else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show lt1)
  Nothing -> error "Typecheck failed: Label not found"
typeCheckC gam sig (ScA n v (DotA y a c1) (DotA z b c2)) vt tr = case Map.lookup n sig of -- SD-Sc
  Just (Lsc _ lt1 lt2) ->
    if check ("SD-Sc: Checking (1) " ++ show v ++ " to be of type " ++ show lt1) (typeCheckV gam sig v lt1 tr) tr
      then if check ("SD-Sc: Checking (2) " ++ show c1 ++ " to be of type " ++ show lt2) (typeCheckC (Map.insert y a gam) sig c1 lt2 tr) tr
        then if check ("SD-Sc: Checking (3) " ++ show c2 ++ " to be of type " ++ show vt) (typeCheckC (Map.insert z b gam) sig c2 vt tr) tr
          then True
          else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt)
        else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show lt2)
      else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show lt1)
  Nothing -> error "Typecheck failed: Label not found"
typeCheckC gam sig (ForA n v (DotA y a c1) (DotA z b c2)) vt tr = case Map.lookup n sig of -- SD-For
  Just (Lfor _ lt) ->
    if check ("SD-For: Checking (1) " ++ show v ++ " to be of type " ++ show (Tlist lt)) (typeCheckV gam sig v (Tlist lt) tr) tr
      then if check ("SD-For: Checking (2) " ++ show c1 ++ " to be of type " ++ show lt) (typeCheckC (Map.insert y a gam) sig c1 lt tr) tr
        then if check ("SD-For: Checking (3) " ++ show c2 ++ " to be of type " ++ show vt) (typeCheckC (Map.insert z b gam) sig c2 vt tr) tr
          then True
        else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt)
      else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show lt)
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show (Tlist lt))
  Nothing -> error "Typecheck failed: Label not found"
typeCheckC gam sig (If v c1 c2) vt tr = -- SD-If
  if check ("SD-If: Checking " ++ show c1 ++ " to be of type " ++ show vt) (typeCheckC gam sig c1 vt tr) tr
    then if check ("SD-If: Checking " ++ show c2 ++ " to be of type " ++ show vt) (typeCheckC gam sig c2 vt tr) tr
      then True
      else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt)
    else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show vt)
typeCheckC gam sig (LetrecA n vt1 v c) vt2 tr = -- SD-Letrec
  if check ("SD-Letrec: Checking (1) " ++ show v ++ " to be of type " ++ show vt1) (typeCheckV (Map.insert n vt1 gam) sig v vt1 tr) tr
    then if check ("SD-Letrec: Checking (2) " ++ show c ++ " to be of type " ++ show vt2) (typeCheckC (Map.insert n vt1 gam) sig c vt2 tr) tr 
      then True
    else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt2)
  else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show vt1)
typeCheckC gam sig (Rec n c1 c2) vt _ = True -- SD-Rec -- TODO
typeCheckC gam sig (Case _ _ _ _ _) vt _ = True -- SD-Case -- TODO
typeCheckC gam sig (Binop _ _ _) vt _ = True -- SD-Binop -- TODO (Assumes operations are well-typed)
typeCheckC gam sig (Unop _ _) vt _ = True -- SD-Unop -- TODO (Assumes operations are well-typed)
typeCheckC _ _ c t _ = False -- error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show t)

typeCheckV :: Gamma -> Sigma -> Value -> ValueType -> Bool -> Bool
typeCheckV _ _ _ Any _ = True
typeCheckV gam sig v (TValVar n) tr = case Map.lookup n gam of -- SD-ValVar
  Just vt -> check ("SD-Var: Checking " ++ show v ++ " to be of type " ++ show vt) (typeCheckV gam sig v vt tr) tr
  Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
typeCheckV gam sig (Var n i) vt tr = case Map.lookup n gam of -- SD-Var
  Just vt' -> check ("SD-Var: Checking " ++ show vt ++ " to be equal to " ++ show vt') (typeEq vt vt') tr
  Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
typeCheckV gam sig Vunit Tunit _ = True -- SD-Unit
typeCheckV gam sig (Vpair (v1, v2)) (Tpair t1 t2) tr = -- SD-Pair
  if check ("SD-First: Checking " ++ show v1 ++ " to be of type " ++ show t1) (typeCheckV gam sig v1 t1 tr) tr
    then if check ("SD-Second: Checking " ++ show v2 ++ " to be of type " ++ show t2) (typeCheckV gam sig v2 t2 tr) tr
      then True
      else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show t2)
    else error ("Typecheck failed: " ++ show v1 ++ " is not of type " ++ show t1)
typeCheckV gam sig (LamA n vt1 c) (Tfunction vt2 vt3) tr = -- SD-Abs
  if check ("SD-Abs: Checking " ++ show c ++ " to be of type " ++ show vt3) (typeCheckC (Map.insert n vt1 gam) sig c vt3 tr) tr
    then True
    else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt3 ++ " in " ++ show (LamA n vt1 c))
typeCheckV gam sig v (Nested t) tr = case v of 
  (Vlist vs) -> if check ("SD-Nested: Checking " ++ show vs ++ " to be of type " ++ show t) (all (\ v -> typeCheckV gam sig v (Nested t) tr) vs) tr
    then True
    else error ("Typecheck failed: " ++ show vs ++ " is not of type " ++ show t)
  v' -> typeCheckV gam sig v' t tr
typeCheckV gam sig (Vlist vs) (Tlist t) tr = -- SD-Nil/SD-Cons (Assumes empty list is always good)
  if check ("SD-List: Checking " ++ show (Vlist vs) ++ " to be of type " ++ show (Tlist t)) (all (\ v -> typeCheckV gam sig v t tr) vs) tr
    then True
    else error ("Typecheck failed: " ++ show vs ++ " is not of type " ++ show t)
typeCheckV gam sig (Vsum (Left v)) (Tsum t1 t2) tr = -- SD-Inl
  if check ("SD-Inl: Checking " ++ show v ++ " to be of type " ++ show t1) (typeCheckV gam sig v t1 tr) tr
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t1)
typeCheckV gam sig (Vsum (Right v)) (Tsum t1 t2) tr = -- SD-Inr
  if check ("SD-Inr: Checking " ++ show v ++ " to be of type " ++ show t2) (typeCheckV gam sig v t2 tr) tr
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t2)
typeCheckV gam sig (Vbool _) Tbool tr = True -- SD-Bool
typeCheckV gam sig (Vint _) Tint tr = True -- SD-Int
typeCheckV gam sig (Vchar _) Tchar tr = True -- SD-Char
typeCheckV gam sig (Vstr _) Tstr tr = True -- SD-Str
typeCheckV gam sig (Vret v) (Tret t) tr = -- SD-Ret
  if typeCheckV gam sig v t tr
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t)
typeCheckV gam sig (Vflag v) (Tflag t) tr = -- SD-Flag
  if typeCheckV gam sig v t tr
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t)
typeCheckV gam sig (Vflag v) (Tret t) tr = -- SD-Ret -- TODO
  if typeCheckV gam sig v t tr
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t)
typeCheckV gam sig (Vret v) (Tflag t) tr = -- SD-Flag -- TODO
  if typeCheckV gam sig v t tr
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t)
typeCheckV gam sig (Vmem m) (Tmem) tr = True -- SD-Mem
typeCheckV gam sig (Vkey k) (Tkey) tr = True -- SD-Key
-- SD-Rec
-- SD-Handler
-- SD-Par
typeCheckV _ _ c t _ = False -- error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show t)

typeEq :: ValueType -> ValueType -> Bool
typeEq Any _ = True
typeEq _ Any = True
typeEq (Tlist t) (Nested t') = typeEq t (Nested t')
typeEq t (Nested t') = typeEq t t'
typeEq Tunit Tunit = True
typeEq (Tpair t1 t2) (Tpair t1' t2') = typeEq t1 t1' && typeEq t2 t2'
typeEq (Tlist t) (Tlist t') = typeEq t t'
typeEq (Tsum t1 t2) (Tsum t1' t2') = typeEq t1 t1' && typeEq t2 t2'
typeEq Tbool Tbool = True
typeEq Tint Tint = True
typeEq Tchar Tchar = True
typeEq Tstr Tstr = True
typeEq (Tret t) (Tret t') = typeEq t t'
typeEq (Tflag t) (Tflag t') = typeEq t t'
typeEq (Tflag t) (Tret t') = typeEq t t'
typeEq (Tret t) (Tflag t') = typeEq t t'
typeEq Tmem Tmem = True
typeEq Tkey Tkey = True
typeEq (Tfunction t1 t2) (Tfunction t1' t2') = typeEq t1 t1' && typeEq t2 t2'
typeEq (TValVar _) t = True
typeEq t (TValVar _) = True
typeEq _ _ = False

rowEq :: EffectType -> EffectType -> Bool
rowEq x y = Set.null (Set.difference x y) && Set.null (Set.difference y x)

transformH :: Gamma -> HTransform -> ValueType -> Bool -> ValueType
transformH gam _ Any _ = Any
transformH gam h (TValVar n) tr = case Map.lookup n gam of 
  Just t -> check ("Handler check (var) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t tr) tr
  Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
transformH gam (UFunction h) (Tfunction _ t) tr = check ("Handler check (function) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t tr) tr
transformH gam h (Tfunction _ t) tr = check ("Handler check (function bypass) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t tr) tr
transformH gam UNone t _ = t
transformH gam (UList h) (Nested t) tr = check ("Handler check (function) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t tr) tr
transformH gam (UList h) (Tlist t) tr = check ("Handler check (function) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t tr) tr
transformH gam (UFirst h) (Tpair f s) tr = check ("Handler check (first) " ++ show h ++ " needs to be of type " ++ show f) (transformH gam h f tr) tr
transformH gam (USecond h) (Tpair f s) tr = check ("Handler check (second) " ++ show h ++ " needs to be of type " ++ show s) (transformH gam h s tr) tr
transformH gam (URet h) (Tret t) tr = check ("Handler check (ret) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t tr) tr
transformH gam (URet h) (Tflag t) tr = check ("Handler check (ret) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t tr) tr
transformH gam (USum h1 h2) (Tsum t1 t2) tr = check ("Handler check (sum) " ++ show h1 ++ " needs to be of type " ++ show t1 ++ " and " ++ show h2 ++ " needs to be of type " ++ show t2) (transformH gam h2 t2 tr) tr
transformH gam h (Tsum t1 t2) tr = check ("Sum forwarding") (transformH gam h t2 tr) tr
transformH _ h t _ = error ("Typecheck failed: " ++ show h ++ " is not compatible with type " ++ show t)

