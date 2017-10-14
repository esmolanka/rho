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

import Data.Text (Text, pack, unpack)
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
    deriving (Eq, Ord)

instance Show Variable where
  showsPrec _ (Variable x) = showString (unpack x)

newtype Label = Label Text
    deriving (Eq, Ord)

instance Show Label where
  showsPrec _ (Label x) = showString "‹" . showString (unpack x) . showString "›"

instance IsString Variable where
  fromString = Variable . fromString

instance IsString Label where
  fromString = Label . fromString

data Const
  = LitInt  Integer
  | LitBool Bool
  | LitStr  String
  | LitUnit

  | ListCons
  | ListEmpty
  | ListFold

  | RecordEmpty
  | RecordSelect Label
  | RecordExtend Label
  | RecordRestrict Label

  | VariantInject Label
  | VariantEmbed Label
  | VariantDecomp Label

  | Delay

  | Add
  | Subtract
  | Multiply
  | Divide

  | Print
  | Read
  | Pure -- limit IO effect

  | Raise
  | Catch

  | Total -- no effects
  deriving (Show, Eq, Ord)

type Expr = Fix ExprF
data ExprF e
  = Var    Position Variable Int
  | Lambda Position Variable e
  | App    Position e e
  | Let    Position Variable e e
  | Const  Position Const
  deriving (Eq, Ord, Functor, Foldable, Traversable)

deriving instance {-# OVERLAPS #-} Eq (Fix ExprF)
deriving instance {-# OVERLAPS #-} Ord (Fix ExprF)

instance Show e => Show (ExprF e) where
  showsPrec n = \case
    Var    _ x i   ->
      showString "{" . showsPrec 11 x . (if i > 0 then showString "/" . showsPrec 11 i else id) . showString "}"
    Lambda _ x e   ->
      showParen (n >= 11)
        (showString "λ" . showsPrec 11 x . showString " → " . showsPrec 11 e)
    App    _ f a   ->
      showParen (n >= 11)
        (showsPrec 11 f . showString " " . showsPrec 11 a)
    Let    _ x a b ->
      showParen (n >= 11)
        (showString "let " . showsPrec 11 x . showString " = " . showsPrec 11 a .
         showString " in " . showsPrec 11 b)
    Const  _ c     ->
      (showsPrec 11 c)

instance {-# OVERLAPS #-} Show (Fix ExprF) where
  showsPrec n (Fix f) = showsPrec n f

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
  | Presence
  deriving (Show, Eq, Ord)

data TyVar = TyVar
  { tvName :: Int
  , tvKind :: Kind
  } deriving (Show, Eq, Ord)

data BaseType
  = TUnit
  | TInt
  | TBool
  | TString
  deriving (Show, Eq, Ord)

type Type = Fix TypeF
data TypeF e
  = TVar TyVar             -- κ
  | T BaseType             -- STAR
  | TArrow e e e           -- STAR (STAR, ROW, STAR)
  | TList e                -- STAR (STAR)
  | TRecord e              -- STAR (ROW)
  | TVariant e             -- STAR (ROW)

  | TPresent               -- PRESENCE
  | TAbsent                -- PRESENCE

  | TRowEmpty              -- ROW ()
  | TRowExtend Label e e e -- ROW (PRESENCE, STAR, ROW)
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
    TRowExtend _ _ _ x -> x
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

simultaneousSubst :: [(TyVar, Type)] -> TySubst
simultaneousSubst subs = TySubst (M.fromList subs)

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

exceptionEff :: Label
exceptionEff = Label (pack "exception")

partialEff :: Label
partialEff = Label (pack "partial")

ioEff :: Label
ioEff = Label (pack "io")

forall :: Kind -> (Type -> TyScheme) -> TyScheme
forall k f =
  let TyScheme bs ty = f (Fix (TVar tv))
      n = case bs of
            [] -> 0
            (TyVar m _ : _) -> m + 1
      tv = TyVar n k
  in  TyScheme (tv : bs) ty

effect :: (Type -> TyScheme) -> TyScheme
effect f = forall Row f

mono :: Type -> TyScheme
mono ty = TyScheme [] ty

infixr 3 ~>

(~>) :: (Type, Type) -> Type -> Type
(a, e) ~> b = Fix (TArrow a e b)

----------------------------------------------------------------------

typeSchemeOfConst :: Const -> TyScheme
typeSchemeOfConst = \case
  LitInt _ ->
    mono $ Fix $ T $ TInt

  LitBool _ ->
    mono $ Fix $ T $ TBool

  LitStr _ ->
    mono $ Fix $ T $ TString

  LitUnit ->
    mono $ Fix $ T $ TUnit

  ListEmpty ->
    forall Star $ \a ->
    mono $ (Fix $ TList a)

  ListCons ->
    forall Star $ \a ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $ (a, e1) ~> (Fix $ TList a, e2) ~> (Fix $ TList a)

  ListFold ->
    forall Star $ \a ->
    forall Star $ \b ->
    effect $ \e1 ->
    effect $ \e2 ->
    effect $ \e3 ->
    effect $ \e4 ->
    mono $
      (((a, e1) ~> (b, e4) ~> b), e2) ~>
      (b, e3) ~>
      (Fix (TList a), e4) ~>
      b


  RecordEmpty ->
    mono $ Fix $ TRecord $ Fix $ TRowEmpty

  RecordSelect label ->
    forall Star $ \a ->
    forall Row  $ \r ->
    effect $ \e ->
    mono $ (Fix $ TRecord $ Fix $ TRowExtend label (Fix TPresent) a r, e) ~> a

  RecordExtend label ->
    forall Star $ \a ->
    forall Star $ \b ->
    forall Row  $ \r ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      (a, e1) ~>
      (Fix $ TRecord $ Fix $ TRowExtend label (Fix TAbsent) b r, e2) ~>
      (Fix $ TRecord $ Fix $ TRowExtend label (Fix TPresent) a r)

  RecordRestrict label ->
    forall Star $ \a ->
    forall Star $ \b ->
    forall Row  $ \r ->
    effect $ \e ->
    mono $
      (Fix $ TRecord $ Fix $ TRowExtend label (Fix TPresent) a r, e) ~>
      (Fix $ TRecord $ Fix $ TRowExtend label (Fix TAbsent) b r)

  VariantInject label  ->
    forall Star $ \a ->
    forall Row  $ \r ->
    effect $ \e ->
    mono $
      (a, e) ~>
      (Fix $ TVariant $ Fix $ TRowExtend label (Fix TPresent) a r)

  VariantEmbed label   ->
    forall Star $ \a ->
    forall Star $ \b ->
    forall Row  $ \r ->
    effect $ \e ->
    mono $
      (Fix $ TVariant $ Fix $ TRowExtend label (Fix TAbsent) a r, e) ~>
      (Fix $ TVariant $ Fix $ TRowExtend label (Fix TPresent) b r)

  VariantDecomp label ->
    forall Star $ \a ->
    forall Star $ \b ->
    forall Star $ \c ->
    forall Row  $ \r ->
    effect $ \e1 ->
    effect $ \e2 ->
    effect $ \e3 ->
    effect $ \e4 ->
    mono $
      (Fix $ TVariant $ Fix $ TRowExtend label (Fix TPresent) a r, e1) ~>
      ( ((a, e2) ~> c, e3) ~>
        (Fix $ TVariant $ Fix $ TRowExtend label (Fix TAbsent) b r, e4) ~>
        c, e4 ) ~>
      c

  Delay ->
    forall Star $ \a ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      ((Fix (T TUnit), e1) ~> a, e2) ~>
      ((Fix (T TUnit), e1) ~> a)

  Add ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      (Fix (T TInt), e1) ~>
      (Fix (T TInt), e2) ~>
      (Fix (T TInt))

  Subtract ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      (Fix (T TInt), e1) ~>
      (Fix (T TInt), e2) ~>
      (Fix (T TInt))

  Multiply ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      (Fix (T TInt), e1) ~>
      (Fix (T TInt), e2) ~>
      (Fix (T TInt))

  Divide ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      (Fix (T TInt), e1) ~>
      (Fix (T TInt), Fix $ TRowExtend partialEff (Fix TPresent) (Fix (T TUnit)) e2) ~>
      (Fix (T TInt))

  Read ->
    effect $ \e1 ->
    mono $
      (Fix (T TUnit), Fix $ TRowExtend ioEff (Fix TPresent) (Fix (T TUnit)) e1) ~>
      (Fix (T TInt))

  Print ->
    effect $ \e1 ->
    mono $
      (Fix (T TInt), Fix $ TRowExtend ioEff (Fix TPresent) (Fix (T TUnit)) e1) ~>
      (Fix (T TUnit))

  Pure ->
    forall Star $ \a ->
    forall Star $ \b ->
    effect $ \e ->
    mono $
      ((Fix (T TUnit), Fix $ TRowExtend ioEff (Fix TAbsent) b e) ~> a, e) ~> a

  Raise ->
    forall Star $ \a ->
    forall Star $ \b ->
    effect $ \e ->
    mono $
      (b, Fix $ TRowExtend exceptionEff (Fix TPresent) b e) ~>
      a

  Catch ->
    forall Star $ \a ->
    forall Star $ \b ->
    forall Star $ \c ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      ((Fix $ T TUnit, Fix $ TRowExtend exceptionEff (Fix TPresent) b e2) ~> a, e1) ~>
      ((b, Fix $ TRowExtend exceptionEff (Fix TAbsent) c e2) ~> a, e2) ~>
      a

  Total ->
    forall Star $ \a ->
    effect $ \e ->
    mono $
      ((Fix (T TUnit), Fix TRowEmpty) ~> a, e) ~> a
