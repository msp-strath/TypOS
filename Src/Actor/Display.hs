{-# LANGUAGE OverloadedStrings #-}

module Actor.Display where

import Control.Monad.Except

import qualified Data.Map as Map

import Actor
import Concrete.Pretty ()
import Display
import Pretty
import Term.Display ()
import Thin
import Unelaboration.Monad (nameOn)
import Unelaboration (DAEnv)

instance Display Env where
  type DisplayEnv Env = ()
  display rho@Env{..} =
    let na = (globalScope, ones (length globalScope), globalScope) in
    fmap collapse $ forM (Map.toList actorVars) $ \ (av, (xs, t)) -> do
      av <- display av
      t <- withEnv (foldl nameOn na xs) $ display t
      pure $ hsep (av : map pretty xs ++ [equals, t])

instance Display ActorMeta where
  type DisplayEnv ActorMeta = ()
  display = viaPretty

instance Display Channel where
  type DisplayEnv Channel = ()
  display = viaPretty

instance Display AActor where
  type DisplayEnv AActor = DAEnv
  display = viaPretty

instance Display (Pat, AActor) where
  type DisplayEnv (Pat, AActor) = DAEnv
  display = viaPretty
