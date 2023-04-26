module Typing where

import Syntax
import Evaluation
import qualified Data.Map as Map
import qualified Data.Set as Set

type Gamma = Map.Map Name ValueType

typeCheckEval :: Comp -> ComputationType -> [(String, Comp)]
typeCheckEval c ct = 
  if typeCheckC Map.empty c ct 
    then case eval1' c of
      (step, Just c') -> (step, c) : typeCheckEval c' ct
      (step, Nothing) -> []
  else [("Typecheck failed", c)]

-- | Evaluation with steps
checkFile :: Comp -> ComputationType -> IO ()
checkFile c ct = do
  let steps = typeCheckEval c ct
  writeFile "typecheck" (prettyprintT steps 1)

-- | Pretty print verbose evaluation
prettyprintT :: [(String, Comp)] -> Int -> String
prettyprintT [] _ = "" 
prettyprintT ((step, c):xs) n = 
  "\n Step: " ++ show n ++ ": " ++ step ++ "\n" ++ show c ++ "\n" ++ prettyprintT xs (n+1) ++ "\n"



typeCheckC :: Gamma -> Comp -> ComputationType -> Bool
typeCheckC gam (Return v) (vt, _) = typeCheckV gam v vt -- SD-Ret
typeCheckC gam (App v1 v2) (vt2, e) = case v1 of
  (LamA n vt1 c) -> typeCheckC (Map.insert n vt1 gam) c (Tfunction vt1 (vt2, e), e)  && typeCheckV gam v2 vt1 -- SD-App
  (Var n _) -> case Map.lookup n gam of
    Just (Tfunction vt1 (vt3, e1)) -> typeCheckV gam v2 vt1 && typeEq vt2 vt3 && rowEq e e1
    Nothing -> False
  _ -> False
typeCheckC gam (DoA n c1 (vt1, e1) c2) (vt2, e2) = typeCheckC (Map.insert n vt1 gam) c2 (vt2, e2) --typeCheckC gam c1 (vt1, e1) -- && typeCheckC (Map.insert n vt1 gam) c2 (vt2, e2) -- SD-Do
typeCheckC gam (LetA n v vt1 c) (vt2, e) = typeCheckV gam v vt1 && typeCheckC (Map.insert n vt1 gam) c (vt2, e) -- SD-Let
typeCheckC gam (HandleA (THandler ct1 (vt1, e1)) h c) (vt2, e2) = typeCheckC gam c ct1 && typeEq vt1 vt2 && rowEq e1 e2 -- SD-Hand
typeCheckC _ _ _ = False 

typeCheckV :: Gamma -> Value -> ValueType -> Bool
typeCheckV gam (Var n i) vt = case Map.lookup n gam of -- SD-Var
  Just vt' -> vt == vt'
  Nothing -> False
typeCheckV gam Vunit Tunit = True -- SD-Unit
typeCheckV gam (Vpair (v1, v2)) (Tpair t1 t2) = typeCheckV gam v1 t1 && typeCheckV gam v2 t2 -- SD-Pair
typeCheckV gam (LamA n vt1 c) (Tfunction vt2 (vt3, e)) = typeCheckC (Map.insert n vt1 gam) c (vt3, e) -- SD-Abs
typeCheckV gam (Vlist vs) (Tlist t) = all (\ v -> typeCheckV gam v t) vs -- SD-Nil/SD-Cons (Assumes empty list is always good)
typeCheckV gam (Vsum (Left v)) (Tsum t1 t2) = typeCheckV gam v t1 -- SD-Inl
typeCheckV gam (Vsum (Right v)) (Tsum t1 t2) = typeCheckV gam v t2 -- SD-Inr
typeCheckV gam (Vbool _) Tbool = True -- SD-Bool
typeCheckV gam (Vint _) Tint = True -- SD-Int
typeCheckV gam (Vchar _) Tchar = True -- SD-Char
typeCheckV gam (Vstr _) Tstr = True -- SD-Str
typeCheckV gam (Vret v) (Tret t) = typeCheckV gam v t -- SD-Ret
typeCheckV gam (Vflag v) (Tflag t) = typeCheckV gam v t -- SD-Flag
typeCheckV gam (Vmem m) (Tmem) = True -- SD-Mem
typeCheckV gam (Vkey k) (Tkey) = True -- SD-Key
-- SD-Rec
-- SD-Handler
-- SD-Par
typeCheckV _ _ _ = False

typeEq :: ValueType -> ValueType -> Bool
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
typeEq (Tfunction t1 (t2, e)) (Tfunction t1' (t2', e')) = typeEq t1 t1' && typeEq t2 t2'
typeEq (TValVar _) t = True
typeEq t (TValVar _) = True
typeEq _ _ = False

rowEq :: EffectType -> EffectType -> Bool
rowEq x y = Set.null (Set.difference x y) && Set.null (Set.difference y x)