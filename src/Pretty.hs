{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty where

import Data.Functor.Foldable (Fix(..), cata)
import Data.String
import Data.Text.Lazy (unpack)

import Types

import Text.PrettyPrint.Leijen.Text hiding ((<$>))

ppTyVar :: TyVar -> Doc
ppTyVar (TyVar n k) = "v" <> int n <> ppKind k
  where
    ppKind Star = "ˢ"
    ppKind Row = "ʳ"

ppBaseType :: BaseType -> Doc
ppBaseType = fromString . show

ppType :: Type -> Doc
ppType = cata $ \case
  TVar tv -> ppTyVar tv
  TConst c -> ppBaseType c
  TArrow f a -> parens (f <+> text "->" <+> a)
  TList a -> brackets a
  TRecord row -> braces row
  TVariant row -> angles row
  TRowEmpty -> text "∅"
  TRowExtend (Label lbl) f t -> textStrict lbl <+> ":" <+> f <> "," <+> t

pp :: Doc -> String
pp = unpack . displayT . renderPretty 0.9 100
