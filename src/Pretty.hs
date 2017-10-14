{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty where

import Data.Functor.Foldable (Fix(..), para)
import Data.String
import Data.Text.Lazy (unpack)

import Types

import Text.PrettyPrint.Leijen.Text hiding ((<$>))

ppTyVar :: TyVar -> Doc
ppTyVar (TyVar n k) = ppKind k <> int n
  where
    ppKind Star     = "α"
    ppKind Row      = "μ"
    ppKind Presence = "θ"

ppBaseType :: BaseType -> Doc
ppBaseType = fromString . drop 1 . show

ppPresence :: Type -> Doc
ppPresence (Fix TPresent) = "▪︎"
ppPresence (Fix TAbsent) = "▫︎"
ppPresence other = "‹" <> ppType other <> "›"

ppType :: Type -> Doc
ppType = para $ \case
  T c -> ppBaseType c
  TVar tv -> ppTyVar tv
  TArrow (_,f) (_,a) -> parens (f <+> text "->" <+> a)
  TList (_,a) -> brackets a
  TRecord (_,row) -> braces row
  TVariant (_,row) -> angles row
  TPresent -> "▪︎"
  TAbsent -> "▫︎"
  TRowEmpty -> text "∅"
  TRowExtend (Label lbl) (p,_) (f',f) (t',t) ->
    let field = case f' of
          Fix (T TUnit) -> textStrict lbl <> ppPresence p
          _             -> textStrict lbl <> ppPresence p <+> ":" <+> f
    in case t' of
         Fix (TRowEmpty) -> field
         Fix (TVar{})    -> field <+> "|" <+> t
         Fix _           -> field <> "," <+> t

pp :: Doc -> String
pp = unpack . displayT . renderPretty 0.9 100
