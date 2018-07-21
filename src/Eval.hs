{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}

module Eval where

import Control.Arrow (first, second)
import Control.Monad.Reader

import Data.Foldable
import Data.Functor.Foldable (Fix(..), cata)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as S

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


freeVars :: Expr -> Set (Variable, Int)
freeVars expr = runReader (cata alg expr) M.empty
  where
    alg :: ExprF (Reader (Map Variable Int) (Set (Variable, Int))) -> Reader (Map Variable Int) (Set (Variable, Int))
    alg = \case
      Var _ x n -> do
        bound <- asks (M.lookup x)
        case bound of
          Just m | m > n -> return S.empty
          _ -> return (S.singleton (x, n))
      Lambda _ x b ->
        local (M.insertWith (+) x 1) b
      Let _ _ x e b -> do
        e' <- e
        b' <- local (M.insertWith (+) x 1) b
        return $ e' <> b'
      other -> fold <$> sequence other


isFreeVar :: Variable -> Int -> Expr -> Bool
isFreeVar x n0 expr = getAny $ runReader (cata alg expr) n0
  where
    alg :: ExprF (Reader Int Any) -> Reader Int Any
    alg = \case
      Var _ x' n' -> do
        n <- ask
        return $ Any (x == x' && n == n')
      Lambda _ x' b ->
        if x == x' then local succ b else b
      Let _ _ x' e b -> do
        e' <- e
        b' <- if x == x' then local succ b else b
        return $ e' <> b'
      other -> fold <$> sequence other


shift :: Int -> Variable -> Expr -> Expr
shift d x e = runReader (cata alg e) 0
  where
    alg :: ExprF (Reader Int Expr) -> Reader Int Expr
    alg = \case
      Var pos x' n -> do
        c <- ask
        return $ Fix $ Var pos x' $
          if x == x' && n >= c then n + d else n
      Lambda pos x' b -> do
        b' <- if x == x' then local succ b else b
        return $ Fix $ Lambda pos x' b'
      Let pos k x' e b -> do
        e' <- e
        b' <- if x == x' then local succ b else b
        return $ Fix $ Let pos k x' e' b'
      other -> Fix <$> sequence other


subst :: Variable -> Int -> Expr -> Expr -> Expr
subst x n0 sub0 expr = runReader (cata alg expr) (n0, sub0)
  where
    succIndex :: Reader (Int, Expr) a -> Reader (Int, Expr) a
    succIndex = local (first succ)

    shifted :: Int -> Variable -> Reader (Int, Expr) a -> Reader (Int, Expr) a
    shifted d x = local (second (shift d x))

    alg :: ExprF (Reader (Int, Expr) Expr) -> Reader (Int, Expr) Expr
    alg = \case
      Var pos x' n' -> do
        (n, sub) <- ask
        if x' == x && n' == n
          then return sub
          else return (Fix (Var pos x' n'))
      Lambda pos x' b -> do
        b' <- shifted 1 x' $
          if x == x'
          then succIndex b
          else b
        return (Fix (Lambda pos x' b'))
      Let pos k x' e b -> do
        e' <- e
        b' <- shifted 1 x' $
          if x == x'
          then succIndex b
          else b
        return (Fix (Let pos k x' e' b'))
      other -> Fix <$> sequence other
