{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE ScopedTypeVariables  #-}

module Main where

import Control.Category ((>>>))
import Data.Semigroup
import qualified Data.Text.Lazy.IO as T

import Language.Sexp
import Language.SexpGrammar

import Sugared
import TypeChecker

main :: IO ()
main = do
  expr <- T.getContents
  either putStrLn (showType . desugar) $ decodeWith sugaredGrammar expr



consGrammar :: Grammar g (([a], a) :- t) ([a] :- t)
consGrammar = partialIso "list" cons uncons
  where
    cons = uncurry $ flip (:)
    uncons [] = Left (unexpected "empty list")
    uncons (x:xs) = Right (xs, x)

addElem
  :: Grammar SexpGrammar (Sexp :- [a] :- t) (a :- [a] :- t)
  -> Grammar SeqGrammar ([a] :- t) ([a] :- t)
addElem g = el g >>> pair >>> consGrammar

terminatedBy
  :: (Eq a) =>
     Grammar SexpGrammar (Sexp :- [a] :- t) (a :- [a] :- t)
  -> Grammar SeqGrammar ([a] :- t) t'
  -> Grammar SeqGrammar t t'
terminatedBy f g =
  push [] >>> go f g
  where
    go f g = (addElem f >>> go f g)
          <> (iso reverse reverse >>> g)

list' :: forall a t. (Eq a) =>
         Grammar SexpGrammar (Sexp :- [a] :- t) (a :- [a] :- t)
      -> Grammar SeqGrammar t ([a] :- t)
list' f = push [] >>> go >>> iso reverse reverse
  where
    go :: Grammar SeqGrammar ([a] :- t) ([a] :- t)
    go = go >>> addElem f


atom :: Grammar SexpGrammar (Sexp :- t) (Atom :- t)
atom = partialOsi "Atom" from to
  where
    from :: Atom -> Sexp
    from atom = Atom dummyPos atom

    to :: Sexp -> Either Mismatch Atom
    to (Atom _ atom) = Right atom
    to _other = Left $ unexpected "atom"


atomInt :: Grammar SexpGrammar (Atom :- t) (Integer :- t)
atomInt = partialOsi "Int" from to
  where
    from :: Integer -> Atom
    from n = AtomInt n

    to :: Atom -> Either Mismatch Integer
    to (AtomInt n) = Right n
    to _other = Left $ expected "integer"

vector :: Grammar SexpGrammar (Sexp :- t) ([Sexp] :- t)
vector = partialOsi "Vector" from to
  where
    from :: [Sexp] -> Sexp
    from = Vector dummyPos

    to :: Sexp -> Either Mismatch [Sexp]
    to (Vector _ children) = Right children
    to _other = Left $ expected "Vector"

uncons :: Grammar g ([a] :- t) (([a], a) :- t)
uncons = partialOsi "list" from to
  where
    to :: [a] -> Either Mismatch ([a], a)
    to [] = Left (unexpected "empty list")
    to (x:xs) = Right (xs, x)

    from :: ([a], a) -> [a]
    from = uncurry $ flip (:)

cons :: Grammar g (([a], a) :- t) ([a] :- t)
cons = partialIso "list" to from
  where
    from :: [a] -> Either Mismatch ([a], a)
    from [] = Left (unexpected "empty list")
    from (x:xs) = Right (xs, x)

    to :: ([a], a) -> [a]
    to = uncurry $ flip (:)
