{-# LANGUAGE OverloadedStrings #-}

module Actor.Display where

import Control.Monad.Except

import qualified Data.Map as Map

import Actor
import Display
import Pattern
import Term.Display ()
import Thin
import Unelaboration (DAEnv, nameOn)

instance Display Env where
  type DisplayEnv Env = ()
  display rho@Env{..} =
    let na = (globalScope, ones (length globalScope), globalScope) in
    fmap collapse $ forM (Map.toList actorVars) $ \ (av, (xs, t)) -> do
    t <- withEnv (foldl nameOn na xs) $ display t
    pure $ concat (show av : map (" " ++) xs ++ [" = ", t])

instance Display ActorMeta where
  type DisplayEnv ActorMeta = ()
  display = viaPretty

instance Display Channel where
  type DisplayEnv Channel = ()
  display = viaPretty

instance Display Actor where
  type DisplayEnv Actor = DAEnv
  display = viaPretty

instance Display (Pat, Actor) where
  type DisplayEnv (Pat, Actor) = DAEnv
  display (p, a) = do
    p <- subdisplay p
    a <- display a
    pure $ p ++ " -> " ++ a
