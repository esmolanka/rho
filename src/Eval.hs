{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}

module Eval where

import Control.Arrow (first)
import Control.Monad.Reader

import Data.Functor.Foldable (Fix(..), cata)

import Data.Map (Map)
import qualified Data.Map as M

import Types


primitives :: Map Variable (Int, Const)
primitives = M.fromList
  [ (Variable "cons",  (0, ListCons))
  , (Variable "nil",   (0, ListEmpty))
  , (Variable "fold",  (0, ListFold))
  , (Variable "read",  (0, Read))
  , (Variable "print", (0, Print))
  , (Variable "pure",  (0, Pure))
  , (Variable "+",     (0, Add))
  , (Variable "-",     (0, Subtract))
  , (Variable "*",     (0, Multiply))
  , (Variable "/",     (0, Divide))
  , (Variable "<",     (0, Compare CmpLT))
  , (Variable "<=",    (0, Compare CmpLE))
  , (Variable ">",     (0, Compare CmpGT))
  , (Variable ">=",    (0, Compare CmpGE))
  , (Variable "==",    (0, Compare CmpEq))
  , (Variable "/=",    (0, Compare CmpNE))
  , (Variable "raise", (0, Raise))
  , (Variable "total", (0, Total))
  , (Variable "catch", (0, Catch))
  , (Variable "fix",   (0, Fixpoint))
  ]


resolvePrimitives :: Expr -> Expr
resolvePrimitives expr = runReader (cata alg expr) primitives
  where
    alg :: ExprF (Reader (Map Variable (Int, Const)) Expr) -> Reader (Map Variable (Int, Const)) Expr
    alg = \case
      Var pos var n -> do
        val <- asks (M.lookup var)
        case val of
          Just (m, c) | n == m -> return (Fix (Const pos c))
          _ -> return (Fix (Var pos var n))

      Lambda pos var body -> do
        body' <- local (M.adjust (first succ) var) body
        return (Fix (Lambda pos var body'))

      App pos f a -> do
        f' <- f
        a' <- a
        return (Fix (App pos f' a'))

      Let pos kind var b a -> do
        b' <- b
        a' <- local (M.adjust (first succ) var) a
        return (Fix (Let pos kind var b' a'))

      Const pos c ->
        return (Fix (Const pos c))


normalize :: Expr -> Expr
normalize = undefined
