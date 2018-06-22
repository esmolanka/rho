{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import qualified Data.ByteString.Lazy.Char8 as B8
import qualified Language.SexpGrammar as Grammar

import Sugared
import TypeChecker

main :: IO ()
main = do
  expr <- B8.getContents

  expr2 <- case Grammar.decodeWith sugaredGrammar "<stdin>" expr of
    Left err -> putStrLn err >> error "Bye"
    Right e -> return e

  either putStrLn B8.putStrLn $ Grammar.encodePrettyWith sugaredGrammar expr2
  showType . desugar $ expr2
