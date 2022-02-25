{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}

module Actor.Display where

import qualified Data.Map as Map
import Data.Maybe

import Control.Monad.Except
import Control.Monad.Reader

import Actor
import Bwd
import Display
import Format
import Hide
import Pattern
import Scope
import Term.Display()

instance Display PatVar where
  display (VarP n) = do
    na@(ns, _, _) <- asks naming
    when (n >= length ns) $ throwError (InvalidNaming na)
    pure (ns <! n)

instance Display Env where
  display (Env sc avs) = pure "ENV"
  {-
  display (Env sc avs) =
    collapse $
    map (\ (av, (xs, t)) -> concat (show av : map (" " ++) xs ++ [" = ", display (foldl nameOn na xs) t])) (Map.toList avs)
-}

instance Display ActorMeta where
  display (ActorMeta str) = pure str

instance Display Channel where
  display (Channel str)  = pure str

instance Display MatchLabel where
  display (MatchLabel str) = pure $ maybe "" ('/' :) str

instance Display Actor where
  display = \case
    a :|: b -> do
      a <- pdisplay a
      b <- pdisplay b
      pure $ a ++ " | " ++ b
    Closure env a -> do
      env <- display env
      a <- pdisplay a
      pure $ unwords ["Closure", env, a]
    Spawn jd ch@(Channel rch) a -> do
      na <- asks naming
      ch <- display0 ch
      a <- local (declareChannel rch) $ display a
      pure $ concat [jd, "@", ch, ". ", a]
    Send ch@(Channel rch) tm a -> do
      ch <- display0 ch
      tm <- inChannel rch $ pdisplay tm
      a <- display a
      pure $ concat [ch, "!", tm, ". ", a]
    Recv ch (av, a) -> do
      ch <- display0 ch
      a <- display a
      pure $ concat [ch, "?", show av, ". ", a]
    FreshMeta (av, a) -> do
      a <- display a
      pure $ concat ["?", show av, ". ", a]
    Under (Scope (Hide x) a) -> do
      a <- local (`nameOn` x) $ display a
      pure $ concat ["\\", x, ". ", a]
    Match tm pts -> do
      tm <- display tm
      pts <- traverse display pts
      pure $ concat ["case ", tm , " " , collapse (BracesList pts) ]
    Constrain s t -> do
      s <- pdisplay s
      t <- pdisplay t
      pure $ unwords [s, "~", t]
    Fail gr -> pure $ unwords ["#\"", gr, "\""]
    Win -> pure $ "Win"
    Print [TermPart Instantiate tm] a -> do
      tm <- pdisplay tm
      a <- pdisplay a
      pure $ unwords ["PRINT", tm, ". ", a]
    Print fmt a -> do
      fmt <- pdisplay fmt
      a <- pdisplay a
      pure $ unwords ["PRINTF", fmt, ". ", a]
    Break str a -> display a

instance Display t => Display (PatF t, Actor) where
  display (p, a) = do
    p <- display p
    a <- display a
    pure $ p ++ " -> " ++ a
