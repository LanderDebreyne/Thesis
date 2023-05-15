module Shared where

import Syntax
import Typing
import Evaluation
import Prelude hiding ((<>))
import Data.Text.IO

-- * Some Auxiliary Functions :

-- | @app2 f v1 v2@ applies the function @f@ to two arguments @v1@ and @v2@.
app2 :: Value -> Value -> Value -> Comp
app2 f v1 v2 = Do "f'" (App f v1) $ App (Var "f'" 0) (shiftV 1 v2)

-- | Generic Algebraic Operation.
op :: Name -> Value -> Comp
op l x = Op l x ("y" :. Return (Var "y" 0))

-- | Generic Scoped Operation.
sc :: Name -> Value -> Dot Name Comp -> Comp
sc l x p = Sc l x p ("z" :. Return (Var "z" 0))

-- | @absurd@ is a function that takes a value and returns an undefined computation.
--   The Undefined computation is used as opposed to the undefined haskell primitive to be able to 
--   print/show intermediate computation steps in the evaluation.
absurd :: Value -> Comp
absurd _ = Undefined


-- | @failure@ is a wrapper for @fail@ with a polymorphic return type.
failure :: Comp
failure = Op "fail" Vunit ("y" :. absurd (Var "y" 0))

-- * Some Auxiliary Functions (Typed):

-- | @app2 f v1 v2@ applies the function @f@ to two arguments @v1@ and @v2@.
app2T :: Value -> Value -> Value -> Comp
app2T f v1 v2 = DoA "f'" (App f v1) Any $ App (Var "f'" 0) (shiftV 1 v2) -- TODO

-- | Generic Algebraic Operation.
opT :: Name -> Value -> ValueType -> Comp
opT l x t = OpA l x (DotA "y" t (Return (Var "y" 0)))

-- | Generic Scoped Operation.
scT :: Name -> Value -> Name -> ValueType -> Comp -> ValueType -> Comp
scT l x n vt c t = ScA l x (DotA n vt c) (DotA "z'" t (Return (Var "z'" 0)))

failureT :: Comp
failureT = OpA "fail" Vunit (DotA "y" Any (absurd (Var "y" 0)))

