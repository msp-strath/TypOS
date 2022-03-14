{-# LANGUAGE OverloadedStrings #-}

module Actor.Display where

import Control.Monad.Except
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map

import Actor
import Display
import Forget
import Format
import Hide
import Pattern
import Pretty
import Scope
import Term.Display (nameOn, initNaming)
import Thin

data DAEnv = DAEnv
  { daActorNaming :: Naming
  , daChannelNaming :: Map Channel Naming
  }

initDAEnv :: DAEnv
initDAEnv = DAEnv initNaming Map.empty

declareChannel :: Channel -> DAEnv -> DAEnv
declareChannel ch rh@DAEnv{..} =
  let update = Map.insert ch daActorNaming in
  rh { daChannelNaming = update daChannelNaming }

updateNaming :: (Naming -> Naming) -> DAEnv -> DAEnv
updateNaming f rh@DAEnv{..} = rh { daActorNaming = f daActorNaming }

setNaming :: Naming -> DAEnv -> DAEnv
setNaming = updateNaming . const

inChannel :: Channel -> DisplayM DAEnv a -> DisplayM DAEnv a
inChannel ch ma = do
  asks (Map.lookup ch . daChannelNaming) >>= \case
    Nothing -> throwError $ UnknownChannel (rawChannel ch)
    Just na -> local (setNaming na) $ ma

instance Forget DAEnv Naming where
  forget = daActorNaming

instance Display Env where
  type DisplayEnv Env = ()
  display rho@Env{..} =
    let na = (globalScope, ones (length globalScope), globalScope) in
    fmap collapse $ forM (Map.toList actorVars) $ \ (av, (xs, t)) -> do
    t <- withEnv (foldl nameOn na xs) $ display t
    pure $ concat (show av : map (" " ++) xs ++ [" = ", t])

instance Display ActorMeta where
  type DisplayEnv ActorMeta = ()
  display (ActorMeta str) = pure str

instance Display Channel where
  type DisplayEnv Channel = ()
  display (Channel str)  = pure str

instance Display Actor where
  type DisplayEnv Actor = DAEnv
  display = \case
    a :|: b -> do
      a <- pdisplay a
      b <- pdisplay b
      pure $ a ++ " | " ++ b
    Spawn jd ch a -> do
      ch' <- subdisplay ch
      a' <- local (declareChannel ch) $ display a
      pure $ concat [jd, "@", ch', ". ", a']
    Send ch tm a -> do
      ch' <- subdisplay ch
      tm' <- inChannel ch $ subpdisplay tm
      a <- display a
      pure $ concat [ch', "!", tm', ". ", a]
    Recv ch (av, a) -> do
      ch <- subdisplay ch
      a <- display a
      pure $ concat [ch, "?", show av, ". ", a]
    FreshMeta cat (av, a) -> do
      a <- display a
      pure $ concat ['\'':cat, "?", show av, ". ", a]
    Under (Scope (Hide x) a) -> do
      a <- local (updateNaming (`nameOn` x)) $ display a
      pure $ concat ["\\", x, ". ", a]
    Push jd (p, t) a -> do
      p <- subdisplay p
      t <- subdisplay t
      a <- display a
      pure $ unwords [jd, "{", p, "->", t, "}.", a]
    Lookup t (av, a) b -> do
      t <- subdisplay t
      a <- display a
      b <- display b
      pure $ unwords ["lookup", t, "{", show av, "->", a, "}", "else", b]
    Match tm pts -> do
      tm <- subdisplay tm
      pts <- traverse display pts
      pure $ concat ["case ", tm , " " , collapse (BracesList pts) ]
    Constrain s t -> do
      s <- subpdisplay s
      t <- subpdisplay t
      pure $ unwords [s, "~", t]
    Win -> pure $ "Win"
    Fail fmt -> do
      fmt <- subpdisplay fmt
      pure $ unwords ["#", fmt]
    Print [TermPart Instantiate tm] a -> do
      tm <- subpdisplay tm
      a <- pdisplay a
      pure $ unwords ["PRINT", tm, ". ", a]
    Print fmt a -> do
      fmt <- subpdisplay fmt
      a <- pdisplay a
      pure $ unwords ["PRINTF", fmt, ". ", a]
    Break fmt a -> do
      fmt <- subpdisplay fmt
      a <- pdisplay a
      pure $ unwords ["BREAK", fmt, ". ", a]

instance Display (Pat, Actor) where
  type DisplayEnv (Pat, Actor) = DAEnv
  display (p, a) = do
    p <- subdisplay p
    a <- display a
    pure $ p ++ " -> " ++ a
