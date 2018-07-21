{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TypeChecker where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader

import Data.Functor.Foldable (cata, para, Fix (..))
import qualified Data.Set as S

import Types
import Context (Context)
import qualified Context as Ctx
import Pretty

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

newtype FreshSupply = FreshSupply { getFreshName :: Int }

newTyVar :: (MonadState FreshSupply m) => Kind -> m Type
newTyVar kind = do
  name <- gets getFreshName
  modify (\s -> s { getFreshName = getFreshName s + 1 })
  return $ Fix $ TVar $ TyVar name kind

instantiate :: forall m. (MonadState FreshSupply m) => TyScheme -> m Type
instantiate TyScheme{..} = do
  subst <- simultaneousSubst <$> mapM mkFreshVar tsForall
  return $ applySubst subst tsBody
  where
    mkFreshVar :: TyVar -> m (TyVar, Type)
    mkFreshVar tv = (,) <$> pure tv <*> newTyVar (tvKind tv)

generalize :: (MonadReader Context m) => Type -> m TyScheme
generalize ty = do
  freeInCtx <- asks freeTyVars
  return (TyScheme (S.toList (freeTyVars ty `S.difference` freeInCtx)) ty)

----------------------------------------------------------------------
-- Unification

unifyBaseTypes :: (?pos :: Position, MonadState FreshSupply m, MonadError TCError m) => BaseType -> BaseType -> m ()
unifyBaseTypes a b =
  unless (a == b) $
    throwError (TCError ?pos (CannotUnify (Fix (T a)) (Fix (T b))))

unifyVars :: (?pos :: Position, MonadState FreshSupply m, MonadError TCError m) => TyVar -> TyVar -> m TySubst
unifyVars a b = do
  unless (tvKind a == tvKind b) $
    throwError (TCError ?pos (KindMismatch (tvKind a) (tvKind b)))
  return (singletonSubst a (Fix (TVar b)))

unifyIs :: (?pos :: Position, MonadState FreshSupply m, MonadError TCError m) => TyVar -> Type -> m TySubst
unifyIs tv typ
  | tv `S.member` freeTyVars typ = throwError (TCError ?pos (InfiniteType typ))
  | otherwise = return (singletonSubst tv typ)

unify :: (?pos :: Position, MonadState FreshSupply m, MonadError TCError m) => Type -> Type -> m TySubst
unify (Fix l) (Fix r) = do
  lk <- inferKind (Fix l)
  rk <- inferKind (Fix r)
  unless (lk == rk) $
    throwError (TCError ?pos (KindMismatch lk rk))
  case (l, r) of
    (TVar x, TVar y) -> unifyVars x y
    (TVar x, typ)    -> x `unifyIs` Fix typ
    (typ,    TVar y) -> y `unifyIs` Fix typ
    (T x,    T y)    -> emptySubst <$ unifyBaseTypes x y

    (TList x,    TList y)    -> unify x y
    (TRecord x,  TRecord y)  -> unify x y
    (TVariant x, TVariant y) -> unify x y
    (TPresent,   TPresent)   -> pure emptySubst
    (TAbsent,    TAbsent)    -> pure emptySubst
    (TArrow a f x, TArrow b g y) -> do
      s1 <- unify a b
      s2 <- unify (applySubst s1 f) (applySubst s1 g)
      let s3 = s2 `composeSubst` s1
      s4 <- unify (applySubst s3 x) (applySubst s3 y)
      pure $ s4 `composeSubst` s3

    (TRowEmpty,  TRowEmpty) -> pure emptySubst

    (TRowExtend lbl pty fty tail, TRowExtend lbl' pty' fty' tail') -> do
      (pty'', fty'', tail'', s1) <- rewriteRow lbl lbl' pty' fty' tail'
      case getRowTail tail of
        Just r | domSubst r s1 ->
                   throwError (TCError ?pos (RecursiveRowType (Fix (TRowExtend lbl' pty'' fty'' tail''))))
        _ -> do
          s2 <- unify (applySubst s1 pty) (applySubst s1 pty'')
          let s3 = composeSubst s2 s1
          s4 <- unify (applySubst s3 fty) (applySubst s3 fty'')
          let s5 = composeSubst s4 s3
          s6 <- unify (applySubst s5 tail) (applySubst s5 tail'')
          return (composeSubst s6 s5)

    (TRowEmpty, TRowExtend lbl p f r) ->
      unify
        (Fix (TRowExtend lbl (Fix TAbsent) f (Fix TRowEmpty)))
        (Fix (TRowExtend lbl p f r))

    (TRowExtend lbl p f r, TRowEmpty) ->
      unify
        (Fix (TRowExtend lbl p f r))
        (Fix (TRowExtend lbl (Fix TAbsent) f (Fix TRowEmpty)))

    _ -> throwError (TCError ?pos (CannotUnify (Fix l) (Fix r)))


rewriteRow
  :: (?pos :: Position, MonadState FreshSupply m, MonadError TCError m) =>
     Label -> Label -> Type -> Type -> Type -> m (Type, Type, Type, TySubst)
rewriteRow newLbl lbl pty fty tail =
  if newLbl == lbl
  then return (pty, fty, tail, emptySubst)
  else
    case tail of
      Fix (TVar alpha) -> do
        beta  <- newTyVar Row
        gamma <- newTyVar Star
        theta <- newTyVar Presence
        s     <- alpha `unifyIs` Fix (TRowExtend newLbl theta gamma beta)
        return (theta, gamma, applySubst s (Fix (TRowExtend lbl pty fty beta)), s)
      Fix (TRowExtend lbl' pty' fty' tail') -> do
        (pty'', fty'', tail'', s) <- rewriteRow newLbl lbl' pty' fty' tail'
        return (pty'', fty'', Fix (TRowExtend lbl pty fty tail''), s)
      Fix TRowEmpty -> do
        gamma <- newTyVar Star
        return (Fix TAbsent, gamma, Fix (TRowExtend lbl pty fty (Fix TRowEmpty)), emptySubst)
      _other ->
        error $ "Unexpected type: " ++ show tail

----------------------------------------------------------------------
-- Type inference

inferType
  :: forall m. (MonadState FreshSupply m, MonadReader Context m, MonadError TCError m) =>
     Expr
  -> m (TySubst, Type, Type)
inferType = para alg
  where
    alg :: ExprF (Expr, m (TySubst, Type, Type)) -> m (TySubst, Type, Type)
    alg = \case
      Var pos x n -> do
        mts <- asks (Ctx.lookup x n)
        case mts of
          Nothing -> throwError (TCError pos (VariableNotFound (Fix (Var pos x n))))
          Just sigma -> do
            typ <- instantiate sigma
            eff <- newTyVar Row
            return
              ( emptySubst
              , typ
              , eff
              )

      Lambda _pos x (_, b) -> do
        tv <- newTyVar Star
        (s1, t1, eff1) <- Ctx.with x (TyScheme [] tv) b
        eff <- newTyVar Row
        return
          ( s1
          , Fix (TArrow (applySubst s1 tv) eff1 t1)
          , eff
          )

      App pos (_, f) (_, a) -> let ?pos = pos in do
        (sf, tf, eff1) <- f
        (sa, ta, eff2) <- Ctx.withSubst sf a
        tr <- newTyVar Star
        sr <- unify (applySubst sa tf) (Fix (TArrow ta eff2 tr))
        se <- unify (applySubst (sr `composeSubst` sa) eff1) (applySubst sr eff2)
        return
          ( se `composeSubst` sr `composeSubst` sa `composeSubst` sf
          , applySubst (se `composeSubst` sr) tr
          , applySubst (se `composeSubst` sr) eff2
          )

      Let pos LetBinding x (_, e) (_, b) -> let ?pos = pos in do
        (se, te, eff1) <- e
        sf <- unify eff1 (Fix TRowEmpty)
        (sb, tb, eff2) <- Ctx.withSubst (sf `composeSubst` se) $ do
          scheme <- generalize te
          Ctx.with x scheme $ b
        return
          ( sb `composeSubst` sf `composeSubst` se
          , tb
          , eff2
          )

      Let pos DoBinding x (_, e) (_, b) -> let ?pos = pos in do
        (se, te, eff1) <- e
        (sb, tb, eff2) <- Ctx.withSubst se $ Ctx.with x (TyScheme [] te) $ b
        sf <- unify eff1 eff2
        return
          ( sb `composeSubst` sf `composeSubst` se
          , tb
          , eff2
          )

      Const _pos c -> do
        typ <- instantiate $ typeSchemeOfConst c
        eff <- newTyVar Row
        return (emptySubst, typ, eff)


inferExprType
  :: forall m. (MonadState FreshSupply m, MonadReader Context m, MonadError TCError m) =>
     Expr -> m (Type, Type)
inferExprType expr = do
  (se, te, fe) <- inferType expr
  return (applySubst se te, applySubst se fe)


inferKind :: forall m. (?pos :: Position, MonadError TCError m) => Type -> m Kind
inferKind = cata (alg <=< sequence)
  where
    alg :: TypeF Kind -> m Kind
    alg = \case
      TVar tv              -> return (tvKind tv)
      T _                  -> return Star
      TArrow Star Row Star -> return Star
      TList Star           -> return Star
      TRecord Row          -> return Star
      TVariant Row         -> return Star
      TPresent             -> return Presence
      TAbsent              -> return Presence
      TRowEmpty            -> return Row
      TRowExtend _
         Presence Star Row -> return Row
      other                -> throwError (TCError ?pos (IllKindedType other))


type InferM = ExceptT TCError (StateT FreshSupply (Reader Context))

primitives :: Context
primitives =
  Ctx.extend (Variable "cons")  (typeSchemeOfConst ListCons) $
  Ctx.extend (Variable "nil")   (typeSchemeOfConst ListEmpty) $
  Ctx.extend (Variable "fold")  (typeSchemeOfConst ListFold) $

  Ctx.extend (Variable "read")  (typeSchemeOfConst Read) $
  Ctx.extend (Variable "print") (typeSchemeOfConst Print) $
  Ctx.extend (Variable "pure")  (typeSchemeOfConst Pure) $

  Ctx.extend (Variable "+")     (typeSchemeOfConst Add) $
  Ctx.extend (Variable "-")     (typeSchemeOfConst Subtract) $
  Ctx.extend (Variable "*")     (typeSchemeOfConst Multiply) $
  Ctx.extend (Variable "/")     (typeSchemeOfConst Divide) $

  Ctx.extend (Variable "<")     (typeSchemeOfConst (Compare CmpLT)) $
  Ctx.extend (Variable "<=")    (typeSchemeOfConst (Compare CmpLE)) $
  Ctx.extend (Variable ">")     (typeSchemeOfConst (Compare CmpGT)) $
  Ctx.extend (Variable ">=")    (typeSchemeOfConst (Compare CmpGE)) $
  Ctx.extend (Variable "==")    (typeSchemeOfConst (Compare CmpEq)) $
  Ctx.extend (Variable "/=")    (typeSchemeOfConst (Compare CmpNE)) $

  Ctx.extend (Variable "raise") (typeSchemeOfConst Raise) $
  Ctx.extend (Variable "total") (typeSchemeOfConst Total) $
  Ctx.extend (Variable "catch") (typeSchemeOfConst Catch) $

  Ctx.extend (Variable "run-state") (typeSchemeOfConst RunState) $

  Ctx.extend (Variable "fix") (typeSchemeOfConst Fixpoint) $

  Ctx.empty

runInfer :: InferM a -> Either TCError a
runInfer =
  flip runReader primitives .
  flip evalStateT (FreshSupply 0) .
  runExceptT

showType :: Expr -> IO ()
showType e = do
  putStrLn ("checking expr:\n" ++ show e ++ "\n\n")
  case runInfer (inferExprType e) of
    Left err -> putStrLn ("typecheck error:\n" ++ show err)
    Right (ty,eff) -> putStrLn $ pp (ppType ty) ++ "\n" ++ pp (ppType eff)
