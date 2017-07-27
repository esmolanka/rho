{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase          #-}

module TypeChecker where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader

import Data.Functor.Foldable (cata, Fix (..))
import qualified Data.Set as S

import Types
import Dsl
import Context (Context)
import qualified Context as Ctx
import Pretty

data TCError
  = CannotUnify Type Type
  | CannotUnifyLabel Label Type
  | InfiniteType Type
  | RecursiveRowType Type
  | KindMismatch Kind Kind
  | VariableNotFound Expr
  deriving (Show)

newtype FreshSupply = FreshSupply { getFreshName :: Int }

newTyVar :: (MonadState FreshSupply m) => Kind -> m Type
newTyVar kind = do
  name <- gets getFreshName
  modify (\s -> s { getFreshName = getFreshName s + 1 })
  return $ Fix $ TVar $ TyVar name kind

instantiate :: forall m. (MonadState FreshSupply m) => TyScheme -> m Type
instantiate TyScheme{..} = do
  subst <- foldSubsts <$> mapM mkFreshVar tsForall
  return $ applySubst subst tsBody
  where
    mkFreshVar :: TyVar -> m TySubst
    mkFreshVar tv = singletonSubst <$> pure tv <*> newTyVar (tvKind tv)

generalize :: (MonadReader Context m) => Type -> m TyScheme
generalize ty = do
  freeInCtx <- asks freeTyVars
  return (TyScheme (S.toList (freeTyVars ty `S.difference` freeInCtx)) ty)

----------------------------------------------------------------------
-- Unification

unifyBaseTypes :: (MonadState FreshSupply m, MonadError TCError m) => BaseType -> BaseType -> m ()
unifyBaseTypes a b =
  unless (a == b) $
    throwError (CannotUnify (Fix (TConst a)) (Fix (TConst b)))

unifyVars :: (MonadState FreshSupply m, MonadError TCError m) => TyVar -> TyVar -> m TySubst
unifyVars a b = do
  unless (tvKind a == tvKind b) $
    throwError (KindMismatch (tvKind a) (tvKind b))
  return (singletonSubst a (Fix (TVar b)))

unifyIs :: (MonadState FreshSupply m, MonadError TCError m) => TyVar -> Type -> m TySubst
unifyIs tv typ
  | tv `S.member` freeTyVars typ = throwError (InfiniteType typ)
  | otherwise = return (singletonSubst tv typ)

unify :: (MonadState FreshSupply m, MonadError TCError m) => Type -> Type -> m TySubst
unify (Fix l) (Fix r) =
  case (l, r) of
    (TVar   x, TVar   y) -> unifyVars x y
    (TVar   x, typ     ) -> x `unifyIs` Fix typ
    (     typ, TVar   y) -> y `unifyIs` Fix typ
    (TConst x, TConst y) -> emptySubst <$ unifyBaseTypes x y
    (TArrow a x, TArrow b y) -> do
      s <- unify a b
      z <- unify (applySubst s x) (applySubst s y)
      pure $ z `composeSubst` s
    (TList x,   TList y) -> unify x y
    (TRecord x, TRecord y) -> unify x y
    (TVariant x, TVariant y) -> unify x y
    (TRowEmpty, TRowEmpty) -> pure emptySubst
    (TRowExtend lbl fty tail, TRowExtend lbl' fty' tail') -> do
      (fty'', tail'', s1) <- rewriteRow lbl lbl' fty' tail'
      case getRowTail tail of
        Just r | domSubst r s1 ->
                   throwError (RecursiveRowType (Fix (TRowExtend lbl' fty'' tail'')))
        _ -> do
          s2 <- unify (applySubst s1 fty) (applySubst s1 fty'')
          let s3 = composeSubst s2 s1
          s4 <- unify (applySubst s3 tail) (applySubst s3 tail'')
          return (composeSubst s4 s3)

    (TRowEmpty, TRowExtend lbl _ _) ->
      throwError $ CannotUnifyLabel lbl (Fix TRowEmpty)

    (TRowExtend lbl _ _, TRowEmpty) ->
      throwError $ CannotUnifyLabel lbl (Fix TRowEmpty)

    _ -> throwError $ CannotUnify (Fix l) (Fix r)

rewriteRow
  :: (MonadState FreshSupply m, MonadError TCError m) =>
     Label -> Label -> Type -> Type -> m (Type, Type, TySubst)
rewriteRow newLbl lbl fty tail =
  if newLbl == lbl
  then return (fty, tail, emptySubst)
  else
    case tail of
      Fix (TVar alpha) -> do
        beta  <- newTyVar Row
        gamma <- newTyVar Star
        s     <- alpha `unifyIs` Fix (TRowExtend newLbl gamma beta)
        return (gamma, applySubst s (Fix (TRowExtend lbl fty beta)), s)
      Fix (TRowExtend lbl' fty' tail') -> do
        (fty'', tail'', s) <- rewriteRow newLbl lbl' fty' tail'
        return (fty'', Fix (TRowExtend lbl fty tail''), s)
      Fix TRowEmpty -> do
        throwError $ CannotUnifyLabel newLbl (Fix TRowEmpty)
      other ->
        error $ "Unexpected type: " ++ show tail

----------------------------------------------------------------------
-- Type inference

inferType
  :: forall m. (MonadState FreshSupply m, MonadReader Context m, MonadError TCError m) =>
     Expr
  -> m (TySubst, Type)
inferType = cata alg
  where
    alg :: ExprF (m (TySubst, Type)) -> m (TySubst, Type)
    alg = \case
      Var pos x n -> do
        mts <- asks (Ctx.lookup x n)
        case mts of
          Nothing -> throwError (VariableNotFound (Fix (Var pos x n)))
          Just sigma -> do
            typ <- instantiate sigma
            return (emptySubst, typ)
      Lambda pos x b -> do
        tv <- newTyVar Star
        (s1, t1) <- Ctx.with x (TyScheme [] tv) b
        return (s1, Fix (TArrow (applySubst s1 tv) t1))
      App pos f a -> do
        (sf, tf) <- f
        (sa, ta) <- Ctx.withSubst sf a
        tr <- newTyVar Star
        sr <- unify (applySubst sa tf) (Fix (TArrow ta tr))
        return (sr `composeSubst` sa `composeSubst` sf, applySubst sr tr)
      Let pos x e b -> do
        (se, te) <- e
        scheme <- Ctx.withSubst se (generalize te)
        (sb, tb) <- Ctx.withSubst se $ Ctx.with x scheme $ b
        return (sb `composeSubst` se, tb)
      Const pos c -> do
        typ <- instantiate $ typeSchemeOfConst c
        return (emptySubst, typ)

inferExprType
  :: forall m. (MonadState FreshSupply m, MonadReader Context m, MonadError TCError m) =>
     Expr
  -> m Type
inferExprType expr = do
  (se, te) <- inferType expr
  return (applySubst se te)

type InferM = ExceptT TCError (StateT FreshSupply (Reader Context))

runInfer :: InferM a -> Either TCError a
runInfer =
  flip runReader  Ctx.empty .
  flip evalStateT (FreshSupply 0) .
  runExceptT

showType :: Expr -> IO ()
showType e =
  case runInfer (inferExprType e) of
    Left e -> error (show e)
    Right ty -> putStrLn $ pp (ppType ty)
