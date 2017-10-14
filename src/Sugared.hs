{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Sugared where

import Prelude hiding (id)
import qualified Types as Raw
import Types hiding (ExprF(..), Const(..))

import Control.Monad.Free
import Data.Functor.Foldable (Fix(..), futu)

import Language.Sexp (Position)
import Language.SexpGrammar
import Language.SexpGrammar.Generic
import Control.Category (id, (>>>))
-- import Control.Monad.State.Strict

import Data.Text (Text)
-- import Data.Semigroup
import Data.Coerce

import GHC.Generics

data Literal
  = LitInt  Integer
  | LitStr  String
  | LitBool Bool
  | LitUnit
    deriving (Generic)

type Sugared = Fix SugaredF
data SugaredF e
  = Var     Position Variable
  | Lambda  Position Variable [Variable] e
  | App     Position e e [e]
  | Let     Position (Variable, e) [(Variable, e)] e
  | Literal Position Literal
  | MkList  Position [e]
  | MkRec   Position [(Label, e)]
  | RecProj Position Label e
  | Delay   Position e
  | Force   Position e
    deriving (Generic)


desugar :: Sugared -> Raw.Expr
desugar = futu coalg
  where
    coalg :: Sugared -> Raw.ExprF (Free Raw.ExprF Sugared)
    coalg = \case
      Fix (Var pos var) ->
        Raw.Var pos var 0

      Fix (Lambda pos b bs e) ->
        Raw.Lambda pos b
          (foldr (\b' rest -> Free $ Raw.Lambda pos b' rest) (Pure e) bs)

      Fix (App pos f a bs) ->
        let Free ap = foldl (\acc arg -> Free $ Raw.App pos acc (Pure arg)) (Pure f) (a:bs)
        in ap

      Fix (Let pos (b, be) bs e) ->
        Raw.Let pos b (Pure be)
          (foldr (\(b', be') rest -> Free $ Raw.Let pos b' (Pure be') rest) (Pure e) bs)

      Fix (Literal pos lit) ->
        case lit of
          LitInt  x -> Raw.Const pos (Raw.LitInt  x)
          LitBool x -> Raw.Const pos (Raw.LitBool x)
          LitStr  x -> Raw.Const pos (Raw.LitStr  x)
          LitUnit   -> Raw.Const pos Raw.LitUnit

      Fix (MkList pos elems) ->
        let nil = Raw.Const pos Raw.ListEmpty
            cons e lst = Raw.App pos (Free (Raw.App pos (Free (Raw.Const pos Raw.ListCons)) e)) lst
        in case foldr (\e rest -> Free $ cons (Pure e) rest) (Free nil) elems of
             Free x -> x
             Pure{} -> error "Woot"

      Fix (MkRec pos elems) ->
        let empty = Raw.Const pos Raw.RecordEmpty
            ext lbl p r = Raw.App pos (Free (Raw.App pos (Free (Raw.Const pos (Raw.RecordExtend lbl))) p)) r
        in case foldr (\(lbl, e) rest -> Free $ ext lbl (Pure e) rest) (Free empty) elems of
             Free x -> x
             Pure{} -> error "Woot"

      Fix (RecProj pos label record) ->
        Raw.App pos
          (Free (Raw.Const pos (Raw.RecordSelect label)))
          (Pure record)

      Fix (Delay pos expr) ->
        Raw.App pos
          (Free (Raw.Const pos Raw.Delay))
          (Free (Raw.Lambda pos (Variable "_") (Pure expr)))

      Fix (Force pos expr) ->
        Raw.App pos
          (Pure expr)
          (Free (Raw.Const pos Raw.LitUnit))


----------------------------------------------------------------------
-- Grammars

varGrammar :: SexpG Variable
varGrammar =
  symbol >>>
  partialOsi "Variable" coerce parseVar
  where
    parseVar :: Text -> Either Mismatch Variable
    parseVar t =
      case t of
        "lambda" -> Left (unexpected t)
        "let"    -> Left (unexpected t)
        "record" -> Left (unexpected t)
        "delay"  -> Left (unexpected t)
        other    -> Right (Variable other)


labelGrammar :: SexpG Label
labelGrammar = keyword >>> iso coerce coerce


bindingGrammar :: SexpG (Variable, Sugared)
bindingGrammar =
  vect (
    el varGrammar >>>
    el sugaredGrammar >>>
    pair
  )


litGrammar :: SexpG Literal
litGrammar = match
  $ With (\liti -> integer >>> liti)
  $ With (\lits -> string' >>> lits)
  $ With (\litb -> bool    >>> litb)
  $ With (\litu -> list id >>> litu)
  $ End


sugaredGrammar :: SexpG Sugared
sugaredGrammar = fixG $ match
  $ With (\var  ->
             position >>>
             swap >>>
             varGrammar >>> var)

  $ With (\lam  ->
            position >>>
            swap >>>
            list (
             el (sym "lambda") >>>
             el (list (
                    el varGrammar >>>
                    rest varGrammar)
                ) >>>
             el sugaredGrammar) >>> lam)

  $ With (\app  ->
            position >>>
            swap >>>
            list (
             el sugaredGrammar >>>
             el sugaredGrammar >>>
             rest sugaredGrammar) >>> app)

  $ With (\let_ ->
            position >>>
            swap >>>
            list (
             el (sym "let") >>>
             el (list (
                    el bindingGrammar >>>
                    rest bindingGrammar)) >>>
             el sugaredGrammar
             ) >>> let_)

  $ With (\mklit ->
             position >>>
             swap >>>
             litGrammar >>>
             mklit)

  $ With (\mklst ->
             position >>>
             swap >>>
             vect (rest sugaredGrammar) >>>
             mklst)

  $ With (\mkrec ->
             position >>>
             swap >>>
             list (el (sym "record") >>>
                   rest (list (el labelGrammar >>> el sugaredGrammar >>> pair))) >>>
             mkrec)

  $ With (\recprj ->
             position >>>
             swap >>>
             list (
               el labelGrammar >>>
               el sugaredGrammar) >>>
             recprj)

  $ With (\delay ->
             position >>>
             swap >>>
             list (el (sym "delay") >>>
                   el sugaredGrammar) >>>
             delay)

  $ With (\force ->
             position >>>
             swap >>>
             list (el sugaredGrammar) >>>
             force)

  $ End


----------------------------------------------------------------------
-- Utils

fixG :: Grammar SexpGrammar (Sexp :- t) (f (Fix f) :- t)
     -> Grammar SexpGrammar (Sexp :- t) (Fix f :- t)
fixG g = g >>> iso coerce coerce
