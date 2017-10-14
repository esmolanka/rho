{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Context
  ( Context (..)
  , empty
  , lookup
  , extend
  , with
  , withSubst
  ) where

import Prelude hiding (lookup)

import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Text.Lazy (fromStrict)
-- import Text.PrettyPrint.Leijen.Text hiding (empty)

import Types


newtype Context = Context (Map Variable [TyScheme])


instance Types Context where
  applySubst subst (Context m) =
    Context $ M.map (map (applySubst subst)) m

  freeTyVars (Context c) =
    foldMap (foldMap freeTyVars) c


empty :: Context
empty = Context M.empty


lookup :: Variable -> Int -> Context -> Maybe TyScheme
lookup v n (Context c) =
  case snd . splitAt n . M.findWithDefault [] v $ c of
    [] -> Nothing
    (x : _) -> Just x


extend :: Variable -> TyScheme -> Context -> Context
extend x e (Context c) =
  Context $ M.alter (addEntry e) x $ c
  where
    addEntry :: TyScheme -> Maybe [TyScheme] -> Maybe [TyScheme]
    addEntry e Nothing = Just [e]
    addEntry e (Just es) = Just (e : es)


with :: forall m a. (MonadReader Context m) => Variable -> TyScheme -> m a -> m a
with x t = local (extend x t)


withSubst :: forall m a. (MonadReader Context m) => TySubst -> m a -> m a
withSubst subst =
  local (applySubst subst)
