module Typing where

import Syntax
import Evaluation
import qualified Data.Map as Map
import qualified Data.Set as Set

type Gamma = Map.Map Name ValueType
type Sigma = Map.Map Name Label

typeCheckEval :: Gamma -> Sigma -> Comp -> ComputationType -> [(String, Comp)]
typeCheckEval gam sig c ct = 
  if typeCheckC gam sig c ct 
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
  if typeCheckV gam sig v vt 
    then True
    else False--error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show vt)
typeCheckC gam sig (App v1 v2) vt2 = case v1 of -- SD-App
  (LamA n vt1 c) -> 
    if typeCheckC (Map.insert n vt1 gam) sig c vt2
      then if typeCheckV gam sig v2 vt1
        then True
        else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show vt1 ++ " in " ++ show (LamA n vt1 c))
      else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show (Tfunction vt1 vt2)) 
  (Var n _) -> case Map.lookup n gam of
    Just (Tfunction vt1 vt3) -> 
      if typeCheckV gam sig v2 vt1
        then if True --typeEq vt2 vt3
          then True
          else error ("Typecheck failed: " ++ show vt2 ++ " is not of type " ++ show vt3)
        else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show vt1)
    Just Any -> True
    Just x -> error ("Typecheck failed: " ++ show x ++ " is not a function")
    Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
  (Lam n c) -> error ("Typecheck failed: " ++ show (Lam n c) ++ " is not annotated")
  _ -> error ("Typecheck failed: " ++ show v1 ++ " is not a function")
typeCheckC gam sig (DoA n c1 vt1 c2) vt2 = -- SD-Do
  if typeCheckC (Map.insert n vt1 gam) sig c2 vt2
    then if typeCheckC gam sig c1 vt1
      then True
      else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show vt1)
    else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt2) 
typeCheckC gam sig (LetA n v vt1 c) vt2 = -- SD-Let
  if typeCheckV gam sig v vt1
    then if typeCheckC (Map.insert n vt1 gam) sig c vt2 
      then True
      else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt2)
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show vt1)
typeCheckC gam sig (HandleA (THandler ct1 vt1) h c) vt2 = -- SD-Hand
  if typeCheckC gam sig c ct1 
    then True
    else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show ct1)
typeCheckC gam sig (OpA n v (DotA y a c)) vt2 = case Map.lookup n sig of -- SD-Op
  Just (Lop _ lt1 lt2) -> 
    if typeCheckV gam sig v lt1 
      then if typeCheckC (Map.insert y a gam) sig c vt2
        then True
        else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt2)
      else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show lt1)
  Nothing -> error "Typecheck failed: Label not found"
typeCheckC gam sig (ScA n v (DotA y a c1) (DotA z b c2)) vt = case Map.lookup n sig of -- SD-Sc
  Just (Lsc _ lt1 lt2) ->
    if typeCheckV gam sig v lt1
      then if typeCheckC (Map.insert y a gam) sig c1 lt2
        then if typeCheckC (Map.insert z b gam) sig c2 vt
          then True
          else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt)
        else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show lt2)
      else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show lt1)
  Nothing -> error "Typecheck failed: Label not found"
typeCheckC gam sig (If v c1 c2) vt = -- SD-If
  if typeCheckC gam sig c1 vt 
    then if typeCheckC gam sig c2 vt
      then True
      else error ("Typecheck failed: " ++ show c2 ++ " is not of type " ++ show vt)
    else error ("Typecheck failed: " ++ show c1 ++ " is not of type " ++ show vt)
typeCheckC gam sig (Binop _ _ _) vt = True -- SD-Binop -- TODO (Assumes operations are well-typed)
typeCheckC gam sig (Unop _ _) vt = True -- SD-Unop -- TODO (Assumes operations are well-typed)
typeCheckC _ _ c t = False -- error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show t)

typeCheckV :: Gamma -> Sigma -> Value -> ValueType -> Bool
typeCheckV _ _ _ Any = True
typeCheckV gam sig v (TValVar n) = case Map.lookup n gam of -- SD-ValVar
  Just vt -> typeCheckV gam sig v vt
  Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
typeCheckV gam sig (Var n i) vt = case Map.lookup n gam of -- SD-Var
  Just vt' -> typeEq vt vt'
  Nothing -> error ("Typecheck failed: " ++ show n ++ " is not in the environment")
typeCheckV gam sig Vunit Tunit = True -- SD-Unit
typeCheckV gam sig (Vpair (v1, v2)) (Tpair t1 t2) = -- SD-Pair
  if typeCheckV gam sig v1 t1 
    then if typeCheckV gam sig v2 t2
      then True
      else error ("Typecheck failed: " ++ show v2 ++ " is not of type " ++ show t2)
    else error ("Typecheck failed: " ++ show v1 ++ " is not of type " ++ show t1)
typeCheckV gam sig (LamA n vt1 c) (Tfunction vt2 vt3) = -- SD-Abs
  if typeCheckC (Map.insert n vt1 gam) sig c vt3 
    then True
    else error ("Typecheck failed: " ++ show c ++ " is not of type " ++ show vt3 ++ " in " ++ show (LamA n vt1 c))
typeCheckV gam sig (Vlist vs) (Tlist t) = -- SD-Nil/SD-Cons (Assumes empty list is always good)
  if all (\ v -> typeCheckV gam sig v t) vs 
    then True
    else error ("Typecheck failed: " ++ show vs ++ " is not of type " ++ show t)
typeCheckV gam sig (Vsum (Left v)) (Tsum t1 t2) = -- SD-Inl
  if typeCheckV gam sig v t1 
    then True
    else error ("Typecheck failed: " ++ show v ++ " is not of type " ++ show t1)
typeCheckV gam sig (Vsum (Right v)) (Tsum t1 t2) = -- SD-Inr
  if typeCheckV gam sig v t2 
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
typeEq Tmem Tmem = True
typeEq Tkey Tkey = True
typeEq (Tfunction t1 t2) (Tfunction t1' t2') = typeEq t1 t1' && typeEq t2 t2'
typeEq (TValVar _) t = True
typeEq t (TValVar _) = True
typeEq _ _ = False

rowEq :: EffectType -> EffectType -> Bool
rowEq x y = Set.null (Set.difference x y) && Set.null (Set.difference y x)