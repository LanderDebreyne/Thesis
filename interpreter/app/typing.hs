module Typing where

import Syntax
import Evaluation
import Debug.Trace
import qualified Data.Map as Map
import qualified Data.Set as Set

type Gamma = Map.Map Name ValueType
type Sigma = Map.Map Name Label

typeCheckEval :: Gamma -> Sigma -> Comp -> ComputationType -> [(String, Comp)]
typeCheckEval gam sig c ct = 
  if trace "---- New step ----" (typeCheckC gam sig c ct) 
    then case eval1' c of
      (step, Just c') -> (step, c) : typeCheckEval gam sig c' ct
      (step, Nothing) -> [("Nothing", c)]
  else [("No more evaluation", c)]

-- | Evaluation with steps
checkFile :: Gamma -> Sigma -> Comp -> ComputationType -> IO ()
checkFile gam sig c ct = do
  let steps = typeCheckEval gam sig c ct
  writeFile "typecheck" (prettyprintT steps 1)

-- | Pretty print verbose evaluation
prettyprintT :: [(String, Comp)] -> Int -> String
prettyprintT [] _ = "" 
prettyprintT ((step, c):xs) n = 
  "\n Step " ++ show n ++ ": " ++ step ++ "\n" ++ show c ++ "\n" ++ prettyprintT xs (n+1) ++ "\n"


typeCheckC :: Gamma -> Sigma -> Comp -> ComputationType -> Bool
typeCheckC _ _ _ Any = True
typeCheckC gam sig (Return v) vt = -- SD-Ret
  if trace ("SD-Ret: Checking " ++ show v ++ " to be of type " ++ show vt) (typeCheckV gam sig v vt) 
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show vt)
typeCheckC gam sig (App v1 v2) vt2 = case v1 of -- SD-App
  (LamA n vt1 c) -> 
    if trace ("SD-App (Lam1): Checking " ++ show c ++ " to be of type " ++ show vt2) (typeCheckC (Map.insert n vt1 gam) sig c vt2)
      then if trace ("SD-App (Lam2): Checking " ++ show v2 ++ " to be of type " ++ show vt1) (typeCheckV gam sig v2 vt1)
        then True
        else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show vt1 ++ " in " ++ show (LamA n vt1 c))
      else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show (Tfunction vt1 vt2)) 
  (Var n _) -> case Map.lookup n gam of
    Just (Tfunction vt1 vt3) -> 
      if trace ("SD-App (Var): Checking " ++ show v2 ++ " to be of type " ++ show vt1) (typeCheckV gam sig v2 vt1)
        then True
        else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show vt1)
    Just Any -> True
    Just x -> error ("Typecheck failed: " ++ show x ++ " is not a function")
    Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
  (Lam n c) -> error ("Typecheck failed: " ++ show (Lam n c) ++ " is not annotated")
  _ -> error ("Typecheck failed: " ++ show v1 ++ " is not a function")
typeCheckC gam sig (DoA n c1 vt1 c2) vt2 = -- SD-Do
  if trace ("SD-Do: Checking " ++ show c2 ++ " to be of type " ++ show vt2) (typeCheckC (Map.insert n vt1 gam) sig c2 vt2)
    then if trace ("SD-Do: Checking " ++ show c1 ++ " to be of type " ++ show vt1) (typeCheckC gam sig c1 vt1)
      then True
      else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show vt1)
    else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt2)
typeCheckC gam sig (LetA n v vt1 c) vt2 = -- SD-Let
  if trace ("SD-Let: Checking " ++ show v ++ " to be of type " ++ show vt1) (typeCheckV gam sig v vt1)
    then if trace ("SD-Let: Checking " ++ show c ++ " to be of type " ++ show vt2)typeCheckC (Map.insert n vt1 gam) sig c vt2 
      then True
      else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt2)
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show vt1)
typeCheckC gam sig (HandleA t h c) vt = -- SD-Hand 
  if trace ("SD-Hand: Checking " ++ show c ++ " to be of type " ++ show vt') (typeCheckC gam sig c vt') 
    then True
    else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt')
    where 
      vt' = transformH gam t vt
typeCheckC gam sig (OpA n v (DotA y a c)) vt2 = case Map.lookup n sig of -- SD-Op
  Just (Lop _ lt1 lt2) -> 
    if trace ("SD-Op: Checking: " ++ show v ++ " to be of type " ++ show lt1) (typeCheckV gam sig v lt1) 
      then if trace ("SD-Op: Checking " ++ show c ++ " to be of type " ++ show vt2) (typeCheckC (Map.insert y a gam) sig c vt2)
        then True
        else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt2)
      else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show lt1)
  Nothing -> error "Typecheck failed: Label not found"
typeCheckC gam sig (ScA n v (DotA y a c1) (DotA z b c2)) vt = case Map.lookup n sig of -- SD-Sc
  Just (Lsc _ lt1 lt2) ->
    if trace ("SD-Sc: Checking " ++ show v ++ " to be of type " ++ show lt1) (typeCheckV gam sig v lt1)
      then if trace ("SD-Sc: Checking " ++ show c1 ++ " to be of type " ++ show lt2) (typeCheckC (Map.insert y a gam) sig c1 lt2)
        then if trace ("SD-Sc: Checking " ++ show c2 ++ " to be of type " ++ show vt) (typeCheckC (Map.insert z b gam) sig c2 vt)
          then True
          else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt)
        else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show lt2)
      else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show lt1)
  Nothing -> error "Typecheck failed: Label not found"
typeCheckC gam sig (If v c1 c2) vt = -- SD-If
  if trace ("SD-If: Checking " ++ show c1 ++ " to be of type " ++ show vt) (typeCheckC gam sig c1 vt) 
    then if trace ("SD-If: Checking " ++ show c2 ++ " to be of type " ++ show vt) (typeCheckC gam sig c2 vt)
      then True
      else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt)
    else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show vt)
typeCheckC gam sig (Binop _ _ _) vt = True -- SD-Binop -- TODO (Assumes operations are well-typed)
typeCheckC gam sig (Unop _ _) vt = True -- SD-Unop -- TODO (Assumes operations are well-typed)
typeCheckC _ _ c t = False -- error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show t)

typeCheckV :: Gamma -> Sigma -> Value -> ValueType -> Bool
typeCheckV _ _ _ Any = True
typeCheckV gam sig v (TValVar n) = case Map.lookup n gam of -- SD-ValVar
  Just vt -> trace ("SD-Var: Checking " ++ show v ++ " to be of type " ++ show vt) (typeCheckV gam sig v vt)
  Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
typeCheckV gam sig (Var n i) vt = case Map.lookup n gam of -- SD-Var
  Just vt' -> trace ("SD-Var: Checking " ++ show vt ++ " to be equal to " ++ show vt') (typeEq vt vt')
  Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
typeCheckV gam sig Vunit Tunit = True -- SD-Unit
typeCheckV gam sig (Vpair (v1, v2)) (Tpair t1 t2) = -- SD-Pair
  if trace ("SD-First: Checking " ++ show v1 ++ " to be of type " ++ show t1) (typeCheckV gam sig v1 t1) 
    then if trace ("SD-Second: Checking " ++ show v2 ++ " to be of type " ++ show t2) (typeCheckV gam sig v2 t2)
      then True
      else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show t2)
    else error ("Typecheck failed: " ++ show v1 ++ " is not of type " ++ show t1)
typeCheckV gam sig (LamA n vt1 c) (Tfunction vt2 vt3) = -- SD-Abs
  if trace ("SD-Abs: Checking " ++ show c ++ " to be of type " ++ show vt3) (typeCheckC (Map.insert n vt1 gam) sig c vt3)
    then True
    else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt3 ++ " in " ++ show (LamA n vt1 c))
typeCheckV gam sig (Vlist vs) (Tlist t) = -- SD-Nil/SD-Cons (Assumes empty list is always good)
  if trace ("SD-List: Checking " ++ show (Vlist vs) ++ " to be of type " ++ show (Tlist t)) (all (\ v -> typeCheckV gam sig v t) vs) 
    then True
    else error ("Typecheck failed: " ++ show vs ++ " is not of type " ++ show t)
typeCheckV gam sig (Vsum (Left v)) (Tsum t1 t2) = -- SD-Inl
  if trace ("SD-Inl: Checking " ++ show v ++ " to be of type " ++ show t1) (typeCheckV gam sig v t1) 
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t1)
typeCheckV gam sig (Vsum (Right v)) (Tsum t1 t2) = -- SD-Inr
  if trace ("SD-Inr: Checking " ++ show v ++ " to be of type " ++ show t2) (typeCheckV gam sig v t2) 
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t2)
typeCheckV gam sig (Vbool _) Tbool = True -- SD-Bool
typeCheckV gam sig (Vint _) Tint = True -- SD-Int
typeCheckV gam sig (Vchar _) Tchar = True -- SD-Char
typeCheckV gam sig (Vstr _) Tstr = True -- SD-Str
typeCheckV gam sig (Vret v) (Tret t) = -- SD-Ret
  if typeCheckV gam sig v t 
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t)
typeCheckV gam sig (Vflag v) (Tflag t) = -- SD-Flag
  if typeCheckV gam sig v t 
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t)
typeCheckV gam sig (Vflag v) (Tret t) = -- SD-Ret -- TODO
  if typeCheckV gam sig v t 
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t)
typeCheckV gam sig (Vret v) (Tflag t) = -- SD-Flag -- TODO
  if typeCheckV gam sig v t 
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t)
typeCheckV gam sig (Vmem m) (Tmem) = True -- SD-Mem
typeCheckV gam sig (Vkey k) (Tkey) = True -- SD-Key
-- SD-Rec
-- SD-Handler
-- SD-Par
typeCheckV _ _ c t = False -- error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show t)

typeEq :: ValueType -> ValueType -> Bool
typeEq Any _ = True
typeEq _ Any = True
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

transformH :: Gamma -> HTransform -> ValueType -> ValueType
transformH gam _ Any = Any
transformH gam h (TValVar n) = case Map.lookup n gam of 
  Just t -> trace ("Handler check (var) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t)
  Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
transformH gam (UFunction h) (Tfunction _ t) = trace ("Handler check (function) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t)
transformH gam h (Tfunction _ t) = trace ("Handler check (function bypass) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t)
transformH gam UNone t = t
transformH gam (UList h) (Tlist t) = trace ("Handler check (function) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t) 
transformH gam (UFirst h) (Tpair f s) = trace ("Handler check (first) " ++ show h ++ " needs to be of type " ++ show f) (transformH gam h f) 
transformH gam (USecond h) (Tpair f s) = trace ("Handler check (second) " ++ show h ++ " needs to be of type " ++ show s) (transformH gam h s)
transformH gam (URet h) (Tret t) = trace ("Handler check (ret) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t)
transformH gam (URet h) (Tflag t) = trace ("Handler check (ret) " ++ show h ++ " needs to be of type " ++ show t) (transformH gam h t)
transformH _ h t = error ("Typecheck failed: " ++ show h ++ " is not compatible with type " ++ show t)

