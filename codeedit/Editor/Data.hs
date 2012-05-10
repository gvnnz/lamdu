{-# LANGUAGE TemplateHaskell, Rank2Types #-}
module Editor.Data (
  Definition(..), atDefBody,
  Builtin(..),
  VariableRef(..), onVariableIRef,
  Lambda(..), atLambdaParamType, atLambdaBody,
  Apply(..), atApplyFunc, atApplyArg,
  Expression(..))
where

import Data.Binary (Binary(..))
import Data.Binary.Get (getWord8)
import Data.Binary.Put (putWord8)
import Data.Derive.Binary(makeBinary)
import Data.DeriveTH(derive)
import Data.Store.IRef (IRef)
import qualified Data.AtFieldTH as AtFieldTH

data Lambda = Lambda {
  lambdaParamType :: IRef Expression,
  lambdaBody :: IRef Expression
  }
  deriving (Eq, Ord, Read, Show)

data Apply = Apply {
  applyFunc :: IRef Expression,
  applyArg :: IRef Expression
  }
  deriving (Eq, Ord, Read, Show)

data Expression =
  ExpressionLambda Lambda |
  ExpressionApply Apply |
  ExpressionGetVariable VariableRef |
  ExpressionHole |
  ExpressionLiteralInteger Integer
  deriving (Eq, Ord, Read, Show)

newtype Definition = Definition {
  defBody :: IRef Expression
  }
  deriving (Eq, Ord, Read, Show)

data Builtin = Builtin {
  biModule :: [String],
  biName :: String
  }
  deriving (Eq, Ord, Read, Show)

data VariableRef
  = ParameterRef { _lambdaRef :: IRef Expression }
  | DefinitionRef (IRef Definition)
  | BuiltinRef (IRef Builtin)
  deriving (Eq, Ord, Read, Show)

onVariableIRef :: (forall a. IRef a -> b) -> VariableRef -> b
onVariableIRef f (ParameterRef i) = f i
onVariableIRef f (DefinitionRef i) = f i
onVariableIRef f (BuiltinRef i) = f i

derive makeBinary ''Apply
derive makeBinary ''Lambda
derive makeBinary ''Builtin
derive makeBinary ''Expression
derive makeBinary ''Definition
derive makeBinary ''VariableRef
AtFieldTH.make ''Definition
AtFieldTH.make ''Lambda
AtFieldTH.make ''Apply
