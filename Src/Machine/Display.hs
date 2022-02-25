module Machine.Display where

import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as Map

import ANSI
import Actor
import Actor.Display()
import Bwd
import Display
import Format
import Machine.Base
import Term
import Thin

instance Display Date where
  display (Date i) = pure $ show i

instance Display Frame where
  display = \case
    Rules jd (ch@(Channel rch), a) -> do
      ch <- display ch
      -- a <- local (declareChannel rch) pdisplay a
      pure $ jd ++ " |-@" ++ ch ++ " {}" -- ++ a
    LeftBranch Hole p -> do
      p <- display p
      pure $ "<> | " ++ p
    RightBranch p Hole -> do
      p <- display p
      pure $ p ++ " | <>"
    Spawnee (Hole, lch) (rch@(Channel ch), p) -> do
      lch <- display lch
      rch <- display rch
      p <- local (declareChannel ch) $ display p
      pure $ "<> @ " ++ lch ++ " | " ++ rch ++ " @ " ++ p
    Spawner (p, lch@(Channel ch)) (rch, Hole) -> do
      p <- local (declareChannel ch . nukeChannels) $ display p
      lch <- display lch
      rch <- display rch
      pure $ p ++ " @ " ++ lch ++ " | " ++ rch ++ " @ <>"
    Sent ch@(Channel rch) t -> do
      ch <- display ch
      t <- inChannel rch $ pdisplay t
      pure $ withANSI [SetColour Foreground Blue, SetWeight Bold] $ "!" ++ ch ++ ". " ++ t
    Pushed jd (p, t) -> do
      p <- display p
      t <- display t
      pure $ unwords [jd, "{", p, "->", t, "}. "]
    Binding x ->
      pure $ withANSI [SetColour Foreground Yellow, SetWeight Bold] $ "\\" ++ x ++ ". "
    UnificationProblem date s t -> do
      s <- display s
      t <- display t
      date <- display0 date
      pure $ withANSI [SetColour Background Red] (s ++ " ~?[" ++ date ++ "] " ++ t)

instance (Show (t Frame), Traversable t, Collapse t, Display s) => Display (Process s t) where
  display p = do
    (fs', store', env', a') <- displayProcess' p
    pure $ concat ["(", collapse fs', " ", store', " ", env', " ", a', ")"]

displayProcess' :: (Traversable t, Collapse t, Display s) =>
  Process s t -> DisplayM (t String, String, String, String)
displayProcess' Process{..} = do
  de <- ask
  (fs', de) <- runStateT (traverse go stack) de
  local (const de) $ do
    store' <- display0 store
    env' <- pdisplay env
    a' <- pdisplay actor
    pure (fs', store', case actor of Win -> ""; _ -> env', a')

    where

    go :: Frame -> StateT DisplayEnv DisplayM String
    go f = do
      de <- get
      dis <- local (const de) $ lift $ display f
      put (de `frameOn` f)
      pure dis

type Store = StoreF Naming

instance Display Store where
  display st = do
    tst <- display (today st)
    sols <- traverse go $ Map.toList $ solutions st
    pure $ tst ++ ": " ++
                 withANSI [SetColour Background Green
                          , SetColour Foreground Black]
                 (collapse sols)
    where
    go :: (Meta, (Naming, Term)) -> DisplayM String
    go (k, (na, t)) = do
      t <- local (setNaming na) $ display t
      k <- display0 k
      pure $ "?" ++ k ++ " := " ++ t

instance Display MachineStep where
  display = \case
    MachineRecv -> pure "recv"
    MachineSend -> pure "send"
    MachineExec -> pure "exec"
    MachineMove -> pure "move"
    MachineUnify -> pure "unify"

frameOn :: DisplayEnv -> Frame -> DisplayEnv
frameOn de = \case
  Binding x -> de `nameOn` x
  Spawnee (Hole, Channel ch) _ -> declareChannel ch $ nukeChannels de
  Spawner _ (Channel ch, Hole) -> declareChannel ch $ de
  _ -> de

frDisplayEnv :: Foldable t => t Frame -> DisplayEnv
frDisplayEnv = foldl frameOn initDisplay

insertDebug :: (Traversable t, Collapse t, Display s)
            => Process s t -> [Format dir Debug a] -> [Format dir String a]
insertDebug p fmt = map go fmt where

  (fs, st, en, _) = either (error . show) id $ evalDisplay (displayProcess' p)
  go = \case
    TermPart d t -> TermPart d t
    StringPart str -> StringPart str
    DebugPart dbg -> DebugPart $ case dbg of
      ShowEnv -> en
      ShowStack -> collapse fs
      ShowStore -> st
