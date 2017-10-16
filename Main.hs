{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE ScopedTypeVariables  #-}

module Main where

import qualified Data.Text.Lazy.IO as T

import qualified Language.SexpGrammar

import Sugared
import TypeChecker

main :: IO ()
main = do
  expr <- T.getContents
  either putStrLn (showType . desugar) $
    Language.SexpGrammar.decodeWith sugaredGrammar expr
