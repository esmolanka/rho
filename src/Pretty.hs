{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty where

import Data.Functor.Foldable (Fix(..), para)
import Data.String
import Data.Text.Lazy (unpack)

import Types

import Text.PrettyPrint.Leijen.Text hiding ((<$>))
import qualified Text.PrettyPrint.Leijen.Text as PP

ppTyVar :: TyVar -> Doc
ppTyVar (TyVar n k) = ppKind k <> int n
  where
    ppKind Star     = "α"
    ppKind Row      = "μ"
    ppKind Presence = "ω"

ppBaseType :: BaseType -> Doc
ppBaseType = fromString . drop 1 . show

ppType :: Type -> Doc
ppType = para $ \case
  T c -> ppBaseType c
  TVar tv -> ppTyVar tv
  TArrow (f',f) (_,e) (_,a) ->
    case f' of
      Fix (TArrow{}) -> parens f <+> "-⟨" <> group e <> "⟩->" <+> a
      _other         -> f <+>  "-⟨" <> group e <> "⟩->" <+> a

  TList (_,a) -> brackets a
  TRecord (_,row)  -> group $ braces $ space <> align (row <> space)
  TVariant (_,row) -> group $ angles $ space <> align (row <> space)
  TPresent -> "▪︎"
  TAbsent -> "▫︎"
  TRowEmpty -> text "∅"
  TRowExtend (Label lbl) (p',_) (f',f) (t',t) ->
    let label = case p' of
          Fix TPresent -> textStrict lbl
          Fix TAbsent  -> "¬" <> textStrict lbl
          other        -> textStrict lbl <> "‹" <> ppType other <> "›"

        field = case (f', p') of
          (Fix (T TUnit), _) -> label
          (_, Fix TAbsent)   -> label
          _                  -> label <+> ":" <+> f

    in case t' of
         Fix (TRowEmpty) -> field
         Fix (TVar{})    -> field <+> "|" <+> t
         Fix _           -> field <> "," PP.<$> t

pp :: Doc -> String
pp = unpack . displayT . renderPretty 0.9 100
