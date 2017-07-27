module Dsl where

import Data.String
import Data.Functor.Foldable (Fix(..))
import Types

import Language.Sexp (dummyPos)

lambda :: String -> Expr -> Expr
lambda x body = Fix $ Lambda dummyPos (fromString x) body

app :: Expr -> [Expr] -> Expr
app f a = foldl ((Fix .) . App dummyPos) f a

let_ :: String -> Expr -> Expr -> Expr
let_ x a b = Fix $ Let dummyPos (fromString x) a b

var :: String -> Expr
var x = Fix $ Var dummyPos (fromString x) 0

int :: Integer -> Expr
int n = Fix $ Const dummyPos $ LitInt n

bool :: Bool -> Expr
bool b = Fix $ Const dummyPos $ LitBool b

rempty :: Expr
rempty =  Fix $ Const dummyPos $ RecordEmpty

rselect :: String -> Expr
rselect lbl = Fix $ Const dummyPos $ RecordSelect (fromString lbl)

rextend :: String -> Fix ExprF
rextend lbl = Fix $ Const dummyPos $ RecordExtend (fromString lbl)

rrestrict :: String -> Fix ExprF
rrestrict lbl = Fix $ Const dummyPos $ RecordRestrict (fromString lbl)

vinject :: String -> Fix ExprF
vinject lbl = Fix $ Const dummyPos $ VariantInject (fromString lbl)

vembed :: String -> Fix ExprF
vembed lbl = Fix $ Const dummyPos $ VariantEmbed (fromString lbl)

vdecomp :: String -> Fix ExprF
vdecomp lbl = Fix $ Const dummyPos $ VariantDecomp (fromString lbl)

nil :: Fix ExprF
nil = Fix $ Const dummyPos $ ListEmpty

cons :: Fix ExprF
cons = Fix $ Const dummyPos $ ListCons
