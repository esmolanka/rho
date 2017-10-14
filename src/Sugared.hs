{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module Sugared where

import qualified Types as Raw
import Types hiding (ExprF(..))

import Control.Monad.Free
import Data.Functor.Foldable (Fix(..), futu)

import Language.Sexp (Position)
import Language.SexpGrammar
import Language.SexpGrammar.Generic
import Control.Category ((>>>))
-- import Control.Monad.State.Strict

import Data.Text (Text)
-- import Data.Semigroup
import Data.Coerce

import GHC.Generics


type Sugared = Fix SugaredF
data SugaredF e
  = Var    Position Variable
  | Lambda Position Variable [Variable] e
  | App    Position e e [e]
  | Let    Position (Variable, e) [(Variable, e)] e
  | MkList Position [e]
  | MkInt  Position Integer
  | MkBool Position Bool
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

      Fix (MkList pos elems) ->
        let nil = Raw.Const pos ListEmpty
            cons e lst = Raw.App pos (Free (Raw.App pos (Free (Raw.Const pos ListCons)) e)) lst
        in case elems of
             [] -> nil
             (x:xs) -> cons (Pure x) (foldr (\e rest -> Free $ cons (Pure e) rest) (Free nil) xs)

      Fix (MkInt pos val) ->
        Raw.Const pos (LitInt val)

      Fix (MkBool pos val) ->
        Raw.Const pos (LitBool val)


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
        other    -> Right (Variable other)

bindingGrammar :: SexpG (Variable, Sugared)
bindingGrammar =
  vect (
    el varGrammar >>>
    el sugaredGrammar >>>
    pair
  )

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

  $ With (\mkl ->
             position >>>
             swap >>>
             vect (rest sugaredGrammar) >>>
             mkl)

  $ With (\mki ->
             position >>>
             swap >>>
             integer >>>
             mki)

  $ With (\mkb ->
             position >>>
             swap >>>
             bool >>>
             mkb)

  $ End



----------------------------------------------------------------------
-- Utils

fixG :: Grammar SexpGrammar (Sexp :- t) (f (Fix f) :- t)
     -> Grammar SexpGrammar (Sexp :- t) (Fix f :- t)
fixG g = g >>> iso coerce coerce
