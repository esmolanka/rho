{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}

module Types where

import Control.Arrow (first, second)
import Control.Monad.Reader

import Data.Text (Text)
import Data.Foldable
import Data.Functor.Foldable (Fix(..), cata)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.String
import Data.Monoid

import Language.Sexp (Position)

----------------------------------------------------------------------
-- Expressions

newtype Variable = Variable Text
    deriving (Show, Eq, Ord)

newtype Label = Label Text
    deriving (Show, Eq, Ord)

instance IsString Variable where
  fromString = Variable . fromString

instance IsString Label where
  fromString = Label . fromString

data Const
  = LitInt  Integer
  | LitBool Bool
  | ListCons
  | ListEmpty
  | RecordEmpty
  | RecordSelect Label
  | RecordExtend Label
  | RecordRestrict Label
  | VariantInject Label
  | VariantEmbed Label
  | VariantDecomp Label
  deriving (Show, Eq, Ord)

type Expr = Fix ExprF
data ExprF e
  = Var    Position Variable Int
  | Lambda Position Variable e
  | App    Position e e
  | Let    Position Variable e e
  | Const  Position Const
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

deriving instance {-# OVERLAPS #-} Eq (Fix ExprF)
deriving instance {-# OVERLAPS #-} Ord (Fix ExprF)
deriving instance {-# OVERLAPS #-} Show (Fix ExprF)

getPosition :: Expr -> Position
getPosition (Fix x) = case x of
  Var pos _ _ -> pos
  App pos _ _ -> pos
  Lambda pos _ _ -> pos
  Let pos _ _ _ -> pos
  Const pos _ -> pos

free :: Variable -> Int -> Expr -> Bool
free x n0 expr = getAny $ runReader (cata alg expr) n0
  where
    alg :: ExprF (Reader Int Any) -> Reader Int Any
    alg = \case
      Var _ x' n' -> do
        n <- ask
        return $ Any (x == x' && n == n')
      Lambda _ x' b ->
        if x == x' then local succ b else b
      Let _ x' e b -> do
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
      Let pos x' e b -> do
        e' <- e
        b' <- if x == x' then local succ b else b
        return $ Fix $ Let pos x' e' b'
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
      Let pos x' e b -> do
        e' <- e
        b' <- shifted 1 x' $
          if x == x'
          then succIndex b
          else b
        return (Fix (Let pos x' e' b'))
      other -> Fix <$> sequence other


----------------------------------------------------------------------
-- Types

class Types a where
  freeTyVars :: a -> S.Set TyVar
  applySubst :: TySubst -> a -> a

data Kind
  = Star
  | Row
  deriving (Show, Eq, Ord)

data TyVar = TyVar
  { tvName :: Int
  , tvKind :: Kind
  } deriving (Show, Eq, Ord)

data BaseType
  = TInt
  | TBool
  deriving (Show, Eq, Ord)

type Type = Fix TypeF
data TypeF e
  = TVar TyVar
  | TConst BaseType
  | TArrow e e
  | TList e
  | TRecord e
  | TVariant e
  | TRowEmpty
  | TRowExtend Label e e
  deriving (Show, Eq, Ord, Functor, Foldable)

instance Types Type where
  freeTyVars =
    cata $ \case
      TVar var -> S.singleton var
      other -> fold other

  applySubst (TySubst s) = cata alg
    where
      alg :: TypeF Type -> Type
      alg = \case
        TVar var ->
          case M.lookup var s of
            Just ty -> ty
            Nothing -> Fix (TVar var)
        other -> Fix other

getRowTail :: Type -> Maybe TyVar
getRowTail =
  cata $ \case
    TRowExtend _ _ x -> x
    TVar v -> Just v
    other -> msum other

deriving instance {-# OVERLAPS #-} Eq (Fix TypeF)
deriving instance {-# OVERLAPS #-} Ord (Fix TypeF)
deriving instance {-# OVERLAPS #-} Show (Fix TypeF)

data TyScheme = TyScheme
  { tsForall :: [TyVar]
  , tsBody   :: Type
  } deriving (Show, Eq, Ord)

instance Types TyScheme where
  freeTyVars ts =
    freeTyVars (tsBody ts) `S.difference` S.fromList (tsForall ts)

  applySubst (TySubst s) (TyScheme binders body) =
    let dummy = M.fromList $ map (\tv -> (tv, ())) binders
        subst = TySubst (s `M.difference` dummy)
    in TyScheme binders (applySubst subst body)

data TySubst = TySubst (M.Map TyVar Type)
  deriving (Show, Eq, Ord)

emptySubst :: TySubst
emptySubst = TySubst M.empty

singletonSubst :: TyVar -> Type -> TySubst
singletonSubst tv typ = TySubst (M.singleton tv typ)

composeSubst :: TySubst -> TySubst -> TySubst
composeSubst (TySubst a) (TySubst b) =
  TySubst $ M.union
    (M.map (applySubst (TySubst a)) b) a

foldSubsts :: [TySubst] -> TySubst
foldSubsts = foldr composeSubst emptySubst

domSubst :: TyVar -> TySubst -> Bool
domSubst tv (TySubst m) = M.member tv m


----------------------------------------------------------------------
-- Types DSL

forall :: Kind -> (Type -> TyScheme) -> TyScheme
forall k f =
  let TyScheme bs ty = f (Fix (TVar tv))
      n = case bs of
            [] -> 0
            (TyVar m _ : _) -> m + 1
      tv = TyVar n k
  in  TyScheme (tv : bs) ty

mono :: Type -> TyScheme
mono ty = TyScheme [] ty

infixr 3 ~>

(~>) :: Type -> Type -> Type
a ~> b = Fix (TArrow a b)

----------------------------------------------------------------------

typeSchemeOfConst :: Const -> TyScheme
typeSchemeOfConst = \case
  LitInt _ ->
    mono $ Fix $ TConst $ TInt

  LitBool _ ->
    mono $ Fix $ TConst $ TBool

  ListEmpty ->
    forall Star $ \a ->
    mono $ (Fix $ TList a)

  ListCons ->
    forall Star $ \a ->
    mono $ a ~> (Fix $ TList a) ~> (Fix $ TList a)

  RecordEmpty ->
    mono $ Fix $ TRecord $ Fix $ TRowEmpty

  RecordSelect label ->
    forall Star $ \a ->
    forall Row  $ \r ->
    mono $ (Fix $ TRecord $ Fix $ TRowExtend label a r) ~> a

  RecordExtend label ->
    forall Star $ \a ->
    forall Row  $ \r ->
    mono $
      a ~> (Fix $ TRecord r) ~> (Fix $ TRecord $ Fix $ TRowExtend label a r)

  RecordRestrict label ->
    forall Star $ \a ->
    forall Row  $ \r ->
    mono $
      (Fix $ TRecord $ Fix $ TRowExtend label a r) ~> (Fix $ TRecord r)

  VariantInject label  ->
    forall Star $ \a ->
    forall Row  $ \r ->
    mono $
      a ~> (Fix $ TVariant $ Fix $ TRowExtend label a r)

  VariantEmbed label   ->
    forall Star $ \a ->
    forall Row  $ \r ->
    mono $
      (Fix $ TVariant r) ~> (Fix $ TVariant $ Fix $ TRowExtend label a r)

  VariantDecomp label  ->
    forall Star $ \a ->
    forall Star $ \b ->
    forall Row  $ \r ->
    mono $
      (Fix $ TVariant $ Fix $ TRowExtend label a r) ~> ((a ~> b) ~> ((Fix $ TVariant r) ~> b) ~> b)
