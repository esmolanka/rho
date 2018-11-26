{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}

module Expr where

import Control.Monad.Reader

import Data.Foldable
import Data.Functor.Compose
import Data.Functor.Classes
import Data.Functor.Classes.Generic
import Data.Functor.Foldable (Fix(..), cata)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.String
import Data.Text (Text, pack, unpack)

import GHC.Generics

import Language.Sexp.Located (Position)

import Types

----------------------------------------------------------------------
-- Expressions

newtype Variable = Variable Text
    deriving (Eq, Ord)

instance Show Variable where
  showsPrec _ (Variable x) = showString (unpack x)

instance IsString Variable where
  fromString = Variable . fromString

data CmpOp
  = CmpLT
  | CmpGT
  | CmpLE
  | CmpGE
  | CmpEq
  | CmpNE
  deriving (Show, Eq, Ord)

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

  | Compare CmpOp

  | And
  | Or
  | Not
  | If

  | Print
  | Read
  | Pure -- limit IO effect

  | Raise
  | Catch
  | Total -- no effects
  | Fixpoint
  deriving (Show, Eq, Ord)

data BindingKind = LetBinding | DoBinding
  deriving (Eq, Ord)

type Expr = Fix ExprF
data ExprF e
  = Var    Position Variable Int
  | Lambda Position Variable e
  | App    Position e e
  | Let    Position BindingKind Variable e e -- let α = e₁ in e₂
  | Const  Position Const
  deriving (Eq, Ord, Functor, Foldable, Traversable, Generic1)

instance Eq1 ExprF where
  liftEq = liftEqDefault

instance Ord1 ExprF where
  liftCompare = liftCompareDefault

instance Show e => Show (ExprF e) where
  showsPrec n = \case
    Var    _ x i   ->
      showString "{" . showsPrec 11 x . (if i > 0 then showString "/" . showsPrec 11 i else id) . showString "}"
    Lambda _ x e   ->
      showParen (n >= 11)
        (showString "λ" . showsPrec 11 x . showString " →\n  " . showsPrec 11 e)
    App    _ f a   ->
      showParen (n >= 11)
        (showsPrec 11 f . showString " " . showsPrec 11 a)
    Let    _ LetBinding x a b ->
      showParen (n >= 11)
        (showString "let " . showsPrec 11 x . showString " = " . showsPrec 11 a .
         showString "\nin " . showsPrec 11 b)
    Let    _ DoBinding x a b ->
      showParen (n >= 11)
        (showString "do " . showsPrec 11 x . showString " <- " . showsPrec 11 a .
         showString ";\n" . showsPrec 11 b)
    Const  _ c     ->
      (showsPrec 11 c)

instance {-# OVERLAPS #-} Show (Fix ExprF) where
  showsPrec n (Fix f) = showsPrec n f


getPosition :: Expr -> Position
getPosition (Fix x) = case x of
  Var pos _ _     -> pos
  App pos _ _     -> pos
  Lambda pos _ _  -> pos
  Let pos _ _ _ _ -> pos
  Const pos _     -> pos

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

  Compare _ ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      (Fix (T TInt), e1) ~>
      (Fix (T TInt), e2) ~>
      (Fix (T TBool))

  And ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      (Fix (T TBool), e1) ~>
      (Fix (T TBool), e2) ~>
      (Fix (T TBool))

  Or ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      (Fix (T TBool), e1) ~>
      (Fix (T TBool), e2) ~>
      (Fix (T TBool))

  Not ->
    effect $ \e1 ->
    mono $
      (Fix (T TBool), e1) ~>
      (Fix (T TBool))

  If ->
    forall Star $ \a ->
    effect $ \e1 ->
    effect $ \e2 ->
    effect $ \e3 ->
    mono $
      (Fix (T TBool), e1) ~>
      ((Fix (T TUnit), e3) ~> a, e2) ~>
      ((Fix (T TUnit), e3) ~> a, e3) ~>
      a

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
      (a, Fix $ TRowExtend exceptionEff (Fix TPresent) a e) ~>
      b

  Catch ->
    forall Star $ \a ->
    forall Star $ \b ->
    forall Star $ \c ->
    forall Presence $ \p ->
    effect $ \e1 ->
    effect $ \e2 ->
    mono $
      ((Fix $ T TUnit, Fix $ TRowExtend exceptionEff (Fix TPresent) b e2) ~> a, e1) ~>
      ((b, Fix (TRowExtend exceptionEff p c e2)) ~> a, Fix (TRowExtend exceptionEff p c e2)) ~>
      a

  Total ->
    forall Star $ \a ->
    effect $ \e ->
    mono $
      ((Fix (T TUnit), Fix TRowEmpty) ~> a, e) ~> a

  Fixpoint ->
    forall Star $ \a ->
    effect $ \e ->
      mono $
        ( (a, e) ~> a
        , Fix $ TRowExtend recEff (Fix TPresent) (Fix (T TUnit)) e
        ) ~> a
