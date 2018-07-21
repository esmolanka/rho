
module Errors where

import Types

data TCError
  = TCError Position Reason
  deriving (Show)

data Reason
  = CannotUnify Type Type
  | CannotUnifyLabel Label Type Type
  | InfiniteType Type
  | RecursiveRowType Type
  | KindMismatch Kind Kind
  | IllKindedType (TypeF Kind)
  | VariableNotFound Expr
  deriving (Show)

