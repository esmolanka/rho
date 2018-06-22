{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

{-# OPTIONS_GHC -O0 #-}

module Sugared where

import Prelude hiding (id)

import Control.Category (id, (>>>))
import Control.Monad.Free
import Data.Coerce
import Data.Functor.Foldable (Fix(..), futu)
import Data.Semigroup
import Data.Text (Text, unpack, isPrefixOf)
import GHC.Generics

import Language.Sexp.Located (Position)
import Language.SexpGrammar
import Language.SexpGrammar.Generic

import qualified Types as Raw
import Types hiding (ExprF(..), Const(..))

data Literal
  = LitInt  Integer
  | LitStr  Text
  | LitBool Bool
  | LitUnit
    deriving (Generic)

data LetBinding e
  = OrdinaryBinding Variable e
  | RecursiveBinding Variable Variable [Variable] e
    deriving (Generic)

data SeqBinding e
  = IgnoringBinding e
  | OrdinarySeqBinding Variable e
    deriving (Generic)

type Sugared = Fix SugaredF
data SugaredF e
  = Var     Position Variable
  | Lambda  Position Variable [Variable] e
  | App     Position e e [e]
  | Let     Position (LetBinding e) [(LetBinding e)] e
  | Literal Position Literal
  | If      Position e e e
  | MkList  Position [e]
  | MkRec   Position [(Label, e)]
  | RecProj Position Label e
  | RecExt  Position Label e e
  | RecRst  Position Label e
  | Delay   Position e
  | Force   Position e
  | DoBlock Position [SeqBinding e]
  | Store   Position Label e
  | Load    Position Label
    deriving (Generic)


desugar :: Sugared -> Raw.Expr
desugar = futu coalg
  where
    dummyVar = Variable "$"

    mkLambda pos bindings e =
      foldr (\b' rest -> Free $ Raw.Lambda pos b' rest) e bindings

    mkApp pos f args =
      foldl (\acc arg -> Free $ Raw.App pos acc arg) f args

    coalg :: Sugared -> Raw.ExprF (Free Raw.ExprF Sugared)
    coalg = \case
      Fix (Var pos var)       -> Raw.Var pos var 0

      Fix (Lambda pos b bs e) -> let Free x = mkLambda pos (b:bs) (Pure e) in x

      Fix (App pos f a as)    -> let Free x = mkApp pos (Pure f) (map Pure (a:as)) in x

      Fix (Let pos b bs e) ->
        let (name, expr) = desugarBinding b
        in Raw.Let pos Raw.LetBinding name expr
             (foldr (\(name, expr) rest -> Free $ Raw.Let pos Raw.LetBinding name expr rest) (Pure e) (map desugarBinding bs))
        where
          desugarBinding :: LetBinding Sugared -> (Variable, Free Raw.ExprF Sugared)
          desugarBinding = \case
            OrdinaryBinding  n expr -> (n, Pure expr)
            RecursiveBinding n var vars expr -> (n, body)
              where
                avs = map (const dummyVar) (var:vars)
                refs = reverse $ zipWith (\var n -> Free $ Raw.Var pos var n) avs [0..]
                body = mkLambda pos avs $ mkApp pos fixpoint (innerBody:refs)
                fixpoint = Free $ Raw.Const pos Raw.Fixpoint
                innerBody = mkLambda pos (n:var:vars) (Pure expr)

      Fix (Literal pos lit) ->
        case lit of
          LitInt  x -> Raw.Const pos (Raw.LitInt  x)
          LitBool x -> Raw.Const pos (Raw.LitBool x)
          LitStr  x -> Raw.Const pos (Raw.LitStr (unpack x))
          LitUnit   -> Raw.Const pos Raw.LitUnit

      Fix (If pos cond tr fls) ->
        let Free x =
              mkApp pos (Free $ Raw.Const pos Raw.If)
                [ Pure cond
                , mkLambda pos [dummyVar] (Pure tr)
                , mkLambda pos [dummyVar] (Pure fls)
                ]
        in x

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

      Fix (RecExt pos label record payload) ->
        Raw.App pos
          (Free (Raw.App pos (Free (Raw.Const pos (Raw.RecordExtend label))) (Pure payload)))
          (Pure record)

      Fix (RecRst pos label record) ->
        Raw.App pos
          (Free (Raw.Const pos (Raw.RecordRestrict label)))
          (Pure record)

      Fix (Delay pos expr) ->
        Raw.App pos
          (Free (Raw.Const pos Raw.Delay))
          (Free (Raw.Lambda pos (Variable "_") (Pure expr)))

      Fix (Force pos expr) ->
        Raw.App pos
          (Pure expr)
          (Free (Raw.Const pos Raw.LitUnit))

      Fix (DoBlock pos stmts) ->
        case stmts of
          [] -> error "Woot"
          stmts@(_:_) ->
            let bind bnd rest =
                  let (var, expr) = case bnd of
                        IgnoringBinding expr -> (Variable "_", expr)
                        OrdinarySeqBinding var expr -> (var, expr)
                  in Free $ Raw.Let pos Raw.DoBinding var (Pure expr) rest
                block = foldr bind (case last stmts of {IgnoringBinding x -> Pure x; OrdinarySeqBinding _ x -> Pure x}) (init stmts)
            in case block of
                 Free x -> x
                 Pure{} -> error "Woot"

      Fix (Store pos label payload) ->
        Raw.App pos (Free (Raw.Const pos (Raw.Store label))) (Pure payload)

      Fix (Load pos label) ->
        Raw.App pos
          (Free (Raw.Const pos (Raw.Load label)))
          (Free (Raw.Const pos Raw.LitUnit))


----------------------------------------------------------------------
-- Grammars

varGrammar :: Grammar Position (Sexp :- t) (Variable :- t)
varGrammar =
  symbol >>>
  partialOsi parseVar coerce
  where
    parseVar :: Text -> Either Mismatch Variable
    parseVar t =
      if t `elem` ["lambda","let","if","record","delay","do","=","?","tt","ff"] ||
         ":" `isPrefixOf` t
      then Left (unexpected t)
      else Right (Variable t)


labelGrammar :: Grammar Position (Sexp :- t) (Label :- t)
labelGrammar = keyword >>> iso coerce coerce


bindingGrammar :: Grammar Position (Sexp :- t) (LetBinding Sugared :- t)
bindingGrammar = match
  $ With (\ordinary ->
            bracketList (
             el varGrammar >>>
             el sugaredGrammar) >>>
            ordinary
         )
  $ With (\recursive ->
            bracketList (
             el (sym ":rec") >>>
             el varGrammar >>>
             el (list (el varGrammar >>> rest varGrammar)) >>>
             el sugaredGrammar) >>>
            recursive)
  $ End


seqStmtGrammar :: Grammar Position (Sexp :- t) (SeqBinding Sugared :- t)
seqStmtGrammar = match
  $ With (\ign -> sugaredGrammar >>> ign)
  $ With (\bnd -> braceList (
             el varGrammar >>>
             el (sym "<-") >>>
             el sugaredGrammar
             ) >>> bnd)
  $ End

boolGrammar :: Grammar Position (Sexp :- t) (Bool :- t)
boolGrammar = symbol >>> partialOsi
  (\case
      "tt" -> Right True
      "ff" -> Right False
      other -> Left $ expected "bool" <> unexpected ("symbol " <> other))
  (\case
      True -> "tt"
      False -> "ff")

litGrammar :: Grammar Position (Sexp :- t) (Literal :- t)
litGrammar = match
  $ With (\liti -> integer >>> liti)
  $ With (\lits -> string  >>> lits)
  $ With (\litb -> boolGrammar >>> litb)
  $ With (\litu -> list id >>> litu)
  $ End


sugaredGrammar :: Grammar Position (Sexp :- t) (Sugared :- t)
sugaredGrammar = fixG $ match
  $ With (\var ->
             annotated "variable" $
             position >>>
             swap >>>
             varGrammar >>> var)

  $ With (\lam ->
             annotated "lambda" $
             position >>>
             swap >>>
             list (
               el (sym "lambda") >>>
               el (list (
                     el varGrammar >>>
                     rest varGrammar)) >>>
               el sugaredGrammar) >>>
             lam)

  $ With (\app ->
            position >>>
            swap >>>
            list (
             el sugaredGrammar >>>
             el sugaredGrammar >>>
             rest sugaredGrammar) >>> app)

  $ With (\let_ ->
             annotated "record literal" $
             position >>>
             swap >>>
             list (
               el (sym "let") >>>
               el (list (
                      el bindingGrammar >>>
                      rest bindingGrammar)) >>>
               el sugaredGrammar) >>>
             let_)

  $ With (\mklit ->
             annotated "literal" $
             position >>>
             swap >>>
             litGrammar >>>
             mklit)

  $ With (\ifp ->
             annotated "if expression" $
             position >>>
             swap >>>
             list (
              el (sym "if") >>>
              el sugaredGrammar >>>
              el sugaredGrammar >>>
              el sugaredGrammar) >>>
             ifp)

  $ With (\mklst ->
             annotated "list literal" $
             position >>>
             swap >>>
             bracketList (rest sugaredGrammar) >>>
             mklst)

  $ With (\mkrec ->
             annotated "record literal" $
             position >>>
             swap >>>
             braceList (
               props (
                 restKeys (
                   sugaredGrammar >>>
                   onTail (iso coerce coerce) >>>
                   pair))) >>>
             mkrec)

  $ With (\recprj ->
             annotated "record selection" $
             position >>>
             swap >>>
             list (
               el labelGrammar >>>
               el sugaredGrammar) >>>
             recprj)

  $ With (\recext ->
             annotated "record extension" $
             position >>>
             swap >>>
             list (
               el labelGrammar >>>
               el sugaredGrammar >>>
               el (sym ":extend") >>>
               el sugaredGrammar) >>>
             recext)

  $ With (\recrest ->
             annotated "record restriction" $
             position >>>
             swap >>>
             list (
               el labelGrammar >>>
               el sugaredGrammar >>>
               el (sym ":restrict")) >>>
             recrest)

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

  $ With (\doblock ->
             annotated "do-block" $
             position >>>
             swap >>>
             list (el (sym "do") >>>
                   el seqStmtGrammar >>>
                   rest seqStmtGrammar >>>
                   onTail cons) >>>
             doblock)

  $ With (\store ->
             position >>>
             swap >>>
             list (el (sym "=") >>>
                   el labelGrammar >>>
                   el sugaredGrammar) >>>
             store)

  $ With (\load ->
             position >>>
             swap >>>
             list (el (sym "?") >>>
                   el labelGrammar) >>>
             load)

  $ End

----------------------------------------------------------------------
-- Utils

fixG :: Grammar Position (Sexp :- t) (f (Fix f) :- t)
     -> Grammar Position (Sexp :- t) (Fix f :- t)
fixG g = g >>> iso coerce coerce
