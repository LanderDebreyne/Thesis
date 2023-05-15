module DepthWithAmb where

-- import Syntax
-- import Shared
-- import Evaluation
-- import Typing
-- import ScopedExamples
-- import ParExamples
-- import TypedScoped
-- import TypedPar
-- import qualified Data.Map as Map

-- ----------------------------------------------------------------
-- -- Depth-Bounded Search with Amb (Untyped)

-- -- Depth-Bounded Search handler that uses parallel Amb for parallel search
-- hDepthAmb :: Handler
-- hDepthAmb = Handler
--   "hDepthAmb" ["choose", "fail"] ["depth"] []
--   ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
--   (\ oplabel -> case oplabel of
--     "fail" -> Just ("_", "_", Return (Vlist []))
--     "choose" -> Just ("x", "k", Return . Lam "d" $
--       Do "b" (Binop Eq (Var "d" 0) (Vint 0)) $
--       If (Var "b" 0) (Return (Vlist []))
--                      (Do "b1" (op "amb" (Vlist [Vbool True, Vbool False])) $
--                       Do "k1" (App (Var "k" 3) (Var "b1" 0)) $
--                       Do "d'" (Binop Add (Var "d" 3) (Vint (-1))) $
--                       App (Var "k1" 1) (Var "d'" 0)))
--     _ -> Nothing)
--   (\ sclabel -> case sclabel of
--     "depth" -> Just ("d'", "p", "k", Return . Lam "d" $
--       Do "p'" (App (Var "p" 2) Vunit) $
--       Do "xs" (App (Var "p'" 0) (Var "d'" 4)) $
--       Binop ConcatMap (Var "xs" 0) (Lam "v_" $ Do "v" (Unop Fst (Var "v_" 0)) $
--                                          Do "k'" (App (Var "k" 5) (Var "v" 0)) $
--                                          App (Var "k'" 0) (Var "d" 5)))
--     _ -> Nothing)
--   (\ forlabel -> case forlabel of 
--     _ -> Nothing)
--   ("f", "p", "k", Return . Lam "d" $ App (Var "f" 3) (Vpair
--     ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
--                 App (Var "p'" 0) (Var "d" 2)
--     , Lam "vs" $ Binop ConcatMap (Var "vs" 0) (Lam "vd" $
--         Do "v" (Unop Fst (Var "vd" 0)) $
--         Do "d" (Unop Snd (Var "vd" 1)) $
--         Do "k'" (App (Var "k" 5) (Var "v" 1)) $
--         App (Var "k'" 0) (Var "d" 1))
--     )))

-- -- Depth-Bounded Search handler that uses parallel Amb for parallel search
-- -- The depth consumed by the scoped computation is also counted in the global depth bound.
-- hDepthAmb2 :: Handler
-- hDepthAmb2 = Handler
--   "hDepthAmb2" ["choose", "fail"] ["depth"] []
--   ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
--   (\ oplabel -> case oplabel of
--     "fail" -> Just ("_", "_", Return (Vlist []))
--     "choose" -> Just ("x", "k", Return . Lam "d" $
--       Do "b" (Binop Eq (Var "d" 0) (Vint 0)) $
--       If (Var "b" 0) (Return (Vlist []))
--                      (Do "b1" (op "amb" (Vlist [Vbool True, Vbool False])) $
--                       Do "k1" (App (Var "k" 3) (Var "b1" 0)) $
--                       Do "d'" (Binop Add (Var "d" 3) (Vint (-1))) $
--                       App (Var "k1" 1) (Var "d'" 0)))
--     _ -> Nothing)
--   (\ sclabel -> case sclabel of
--     "depth" -> Just ("d'", "p", "k", Return . Lam "d" $
--       Do "p'" (App (Var "p" 2) Vunit) $
--       Do "md" (Binop Min (Var "d'" 4) (Var "d" 1)) $
--       Do "xs" (App (Var "p'" 1) (Var "md" 0)) $
--       Binop ConcatMap (Var "xs" 0) (Lam "vd" $ Do "v" (Unop Fst (Var "vd" 0)) $
--                                          Do "rd" (Unop Snd (Var "vd" 1)) $
--                                          Do "consumed" (Binop Minus (Var "md" 4) (Var "rd" 0)) $
--                                          Do "trued" (Binop Minus (Var "d" 7) (Var "consumed" 0)) $
--                                          Do "k'" (App (Var "k" 9) (Var "v" 3)) $
--                                          App (Var "k'" 0) (Var "trued" 1)))
--     _ -> Nothing)
--   (\ forlabel -> case forlabel of
--     _ -> Nothing)
--   ("f", "p", "k", Return . Lam "d" $ App (Var "f" 3) (Vpair
--     ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
--                 App (Var "p'" 0) (Var "d" 2)
--     , Lam "vs" $ Binop ConcatMap (Var "vs" 0) (Lam "vd" $
--         Do "v" (Unop Fst (Var "vd" 0)) $
--         Do "d" (Unop Snd (Var "vd" 1)) $
--         Do "k'" (App (Var "k" 5) (Var "v" 1)) $
--         App (Var "k'" 0) (Var "d" 1))
--     )))

-- -- | Depth-Bounded Search with Amb using first handler
-- ------
-- exDepthAmb1 = hPure # hAmb # (Do "f" (hDepthAmb # cDepth) $ App (Var "f" 0) (Vint 2))
-- -- Usage: evalFileFlat $ hPure # hAmb # (Do "f" (hDepthAmb # cDepth) $ App (Var "f" 0) (Vint 2))
-- ------

-- -- | Depth-Bounded Search with Amb using second handler
-- ------
-- exDepthAmb2 = hPure # hAmb # (Do "f" (hDepthAmb2 # cDepth) $ App (Var "f" 0) (Vint 2))
-- -- Usage: evalFileFlat $ hPure # hAmb # (Do "f" (hDepthAmb2 # cDepth) $ App (Var "f" 0) (Vint 2))
-- ------


-- --------------------------------------------------------------------------------------------------------------------
-- -- Depth-Bounded Search with Amb (Typed)

-- -- Depth-Bounded Search handler that uses parallel Amb for parallel search
-- hDepthAmbT :: Handler
-- hDepthAmbT = Handler
--   "hDepthAmb" ["choose", "fail"] ["depth"] []
--   ("x", Return . LamA "d" Tint $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
--   (\ oplabel -> case oplabel of
--     "fail" -> Just ("_", "_", Return (Vlist []))
--     "choose" -> Just ("x", "k", Return . LamA "d" Tint $
--       DoA "b" (Binop Eq (Var "d" 0) (Vint 0)) Tbool $
--       If (Var "b" 0) (Return (Vlist []))
--                      (DoA "b1" (OpA "amb" (Vlist [Vbool True, Vbool False]) (DotA "y" Any (Return (Var "y" 0)))) Tbool $
--                       DoA "k1" (App (Var "k" 3) (Var "b1" 0)) (Tfunction Tint Any) $
--                       DoA "d'" (Binop Add (Var "d" 3) (Vint (-1))) Tint $
--                       App (Var "k1" 1) (Var "d'" 0)))
--     _ -> Nothing)
--   (\ sclabel -> case sclabel of
--     "depth" -> Just ("d'", "p", "k", Return . LamA "d" Tint $
--       DoA "p'" (App (Var "p" 2) Vunit) (Tfunction Tint (Tlist Any)) $
--       DoA "xs" (App (Var "p'" 0) (Var "d'" 4)) (Tlist Any) $
--       Binop ConcatMap (Var "xs" 0) (LamA "v_" (Tpair Any Any) $ DoA "v" (Unop Fst (Var "v_" 0)) Any $
--                                          DoA "k'" (App (Var "k" 5) (Var "v" 0)) (Tfunction Tint Any) $
--                                          App (Var "k'" 0) (Var "d" 5)))
--     _ -> Nothing)
--   (\ forlabel -> case forlabel of 
--     _ -> Nothing)
--   ("f", "p", "k", Return . LamA "d" Tint $ App (Var "f" 3) (Vpair
--     ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any) $
--                 App (Var "p'" 0) (Var "d" 2)
--     , LamA "vs" (Tlist Any) $ Binop ConcatMap (Var "vs" 0) (LamA "vd" (Tpair Any Tint) $
--         DoA "v" (Unop Fst (Var "vd" 0)) Any $
--         DoA "d" (Unop Snd (Var "vd" 1)) Tint $
--         DoA "k'" (App (Var "k" 5) (Var "v" 1)) (Tfunction Tint Any) $
--         App (Var "k'" 0) (Var "d" 1))
--     )))

-- -- Depth-Bounded Search handler that uses parallel Amb for parallel search
-- -- The depth consumed by the scoped computation is also counted in the global depth bound.
-- hDepthAmb2T :: Handler
-- hDepthAmb2T = Handler
--   "hDepthAmb2" ["choose", "fail"] ["depth"] []
--   ("x", Return . LamA "d" Tint $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
--   (\ oplabel -> case oplabel of
--     "fail" -> Just ("_", "_", Return (Vlist []))
--     "choose" -> Just ("x", "k", Return . LamA "d" Tint $
--       DoA "b" (Binop Eq (Var "d" 0) (Vint 0)) Tbool $
--       If (Var "b" 0) (Return (Vlist []))
--                      (DoA "b1" (OpA "amb" (Vlist [Vbool True, Vbool False]) (DotA "y" Any (Return (Var "y" 0)))) Tbool $
--                       DoA "k1" (App (Var "k" 3) (Var "b1" 0)) (Tfunction Tint Any) $
--                       DoA "d'" (Binop Add (Var "d" 3) (Vint (-1))) Tint $
--                       App (Var "k1" 1) (Var "d'" 0)))
--     _ -> Nothing)
--   (\ sclabel -> case sclabel of
--     "depth" -> Just ("d'", "p", "k", Return . LamA "d" Tint $
--       DoA "p'" (App (Var "p" 2) Vunit) (Tfunction Tint (Tlist Any)) $
--       DoA "md" (Binop Min (Var "d'" 4) (Var "d" 1)) Tint $
--       DoA "xs" (App (Var "p'" 1) (Var "md" 0)) (Tlist Any) $
--       Binop ConcatMap (Var "xs" 0) (LamA "vd" (Tpair Any Tint) $ DoA "v" (Unop Fst (Var "vd" 0)) Any $
--                                          DoA "rd" (Unop Snd (Var "vd" 1)) Tint $
--                                          DoA "consumed" (Binop Minus (Var "md" 4) (Var "rd" 0)) Tint $
--                                          DoA "trued" (Binop Minus (Var "d" 7) (Var "consumed" 0)) Tint $
--                                          DoA "k'" (App (Var "k" 9) (Var "v" 3)) (Tfunction Tint Any)$
--                                          App (Var "k'" 0) (Var "trued" 1)))
--     _ -> Nothing)
--   (\ forlabel -> case forlabel of
--     _ -> Nothing)
--   ("f", "p", "k", Return . LamA "d" Tint $ App (Var "f" 3) (Vpair
--     ( LamA "y" Any $ DoA "p'" (App (Var "p" 3) (Var "y" 0)) (Tfunction Tint Any) $
--                 App (Var "p'" 0) (Var "d" 2)
--     , LamA "vs" (Tlist Any) $ Binop ConcatMap (Var "vs" 0) (LamA "vd" (Tpair Any Tint) $
--         DoA "v" (Unop Fst (Var "vd" 0)) Any $
--         DoA "d" (Unop Snd (Var "vd" 1)) Tint $
--         DoA "k'" (App (Var "k" 5) (Var "v" 1)) (Tfunction Tint Any) $
--         App (Var "k'" 0) (Var "d" 1))
--     )))


-- tDepthAmbSig = Map.fromList([
--   ("accum", Lop "accum" (Tpair Tint Tint) (Tpair (Tlist Any) (Tlist Tunit))),
--   ("amb", Lop "amb" (Tlist Tbool) Tint),
--   ("for", Lfor "for" Any)
--   ])


-- -- | Depth-Bounded Search with Amb using first handler
-- ------
-- tDepthAmbComp1 = HandleA UNone hPureT (HandleA (UList UNone) hAmbT (DoA "f" (HandleA (UList UNone) hDepthAmbT cDepthT) (Tfunction Tint Any) $ App (Var "f" 0) (Vint 2)))
-- -- Typechecking
-- tDepthAmb1 = checkFile Map.empty tDepthAmbSig tDepthAmbComp1 (Nested (Tpair Tint Tint))
-- ------

-- -- | Depth-Bounded Search with Amb using second handler
-- ------
-- tDepthAmbComp2 = HandleA UNone hPureT (HandleA (UList UNone) hAmbT (DoA "f" (HandleA (UList UNone) hDepthAmb2T cDepthT) (Tfunction Tint Any) $ App (Var "f" 0) (Vint 2)))
-- -- Typechecking
-- tDepthAmb2 = checkFile Map.empty tDepthAmbSig tDepthAmbComp2 (Nested (Tpair Tint Tint))
-- ------






