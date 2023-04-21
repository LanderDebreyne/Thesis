module Typing where

import Syntax

-- -- | Type scheme syntax
-- data TypeScheme = Tval ValueType
--                  | TforAllEffect Name Int TypeScheme
--                  | TforAllValue Name Int TypeScheme
--                  deriving (Eq, Show)


-- typeCheck :: Comp -> ComputationType -> Bool
-- typeCheck (Return v) () = 

-- -- | Typing function
-- typeComp :: Comp -> EffectType -> ComputationType
-- typeComp (Return v) e = (typeValue v, e) -- T-Return
-- typeComp (App v1 v2) e = case typeValue v1 of
--     Tfunction t1 t2 -> if typeEqV t1 (typeValue v2) then t2 else error "type error"
--     _ -> error "type error" -- T-App
-- -- typeComp (Let x v c2) e = typeComp c2 -- T-Let 

-- TODO?
-- typeEqV :: ValueType -> ValueType -> Bool
-- typeEqV Tunit Tunit = True
-- typeEqV (Tpair t1 t2) (Tpair t3 t4) = typeEqV t1 t3 && typeEqV t2 t4
-- typeEqV (Tfunction t1 t2) (Tfunction t3 t4) = typeEqV t1 t3 && typeEqC t2 t4
-- typeEqV (THandler t1 t2) (THandler t3 t4) = typeEqC t1 t3 && typeEqC t2 t4
-- typeEqV (Tlist t1) (Tlist t2) = typeEqV t1 t2
-- typeEqV (TValVar x i) (TValVar y j) = x == y && i == j
-- typeEqV (TOpAbs x i t1) (TOpAbs y j t2) = x == y && i == j && typeEqV t1 t2
-- typeEqV (Tapp t1 t2) (Tapp t3 t4) = typeEqV t1 t3 && typeEqV t2 t4
-- typeEqV (Tsum t1 t2) (Tsum t3 t4) = typeEqV t1 t3 && typeEqV t2 t4
-- typeEqV t1 t2 = if typeEqV t2 t1 then True else False

-- typeEqC :: ComputationType -> ComputationType -> Bool
-- typeEqC (t1, e1) (t2, e2) = typeEqV t1 t2 && e1 == e2

-- typeValue :: Value -> ValueType
-- typeValue Vunit = Tunit -- T-Unit
-- -- typeValue (Var x i) = 
-- -- typeValue (Lam x c) =

-- typeValue (Vpair (v1, v2)) = Tpair (typeValue v1) (typeValue v2) -- T-Pair
-- typeValue (Vhandler h) = typeHandler h -- T-Handler
-- typeValue (Vlist vs) = Tlist (typeValue (head vs)) -- T-List
-- -- typeValue (Vrec x v1 v2) = 
-- typeValue (Vsum (Left v)) = typeValue v -- T-Sum
-- typeValue (Vsum (Right v)) = typeValue v -- T-Sum
-- -- T-Var
-- -- T-Abs
-- -- T-EqV

-- -- T-Var

-- typeHandler :: Handler -> ValueType