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
    Rules jd (ch, a) -> do
      ch <- display ch
      -- a <- pdisplay a
      pure $ jd ++ " |-@" ++ ch ++ " {}" -- ++ a
    RulePatch jd ml i env a -> do
      ml <- display0 ml
      -- env <- display env
      -- a <- display a
      pure $ jd ++ ml ++ " |- +" ++ " " ++ show i ++ " -> {}"{- ++ env ++ " " ++ a -}
    LeftBranch Hole p -> do
      p <- display p
      pure $ "<> | " ++ p
    RightBranch p Hole -> do
      p <- display p
      pure $ p ++ " | <>"
    Spawnee (Hole, lch) (rch, p) -> do
      lch <- display lch
      rch <- display rch
      p <- display p
      pure $ "<> @ " ++ lch ++ " | " ++ rch ++ " @ " ++ p
    Spawner (p, lch) (rch, Hole) -> do
      p <- display p
      lch <- display lch
      rch <- display rch
      pure $ p ++ " @ " ++ lch ++ " | " ++ rch ++ " @ <>"
    Sent ch t -> do
      ch <- display ch
      t <- display t
      pure $ withANSI [SetColour Foreground Blue, SetWeight Bold] $ "!" ++ ch ++ ". " ++ t
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
      case f of
        Binding x -> put (de `nameOn` x)
        _ -> pure ()
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

frnaming :: Foldable t => t Frame -> Naming
frnaming zf = (zv, ones (length zv), zv)
 where
  zv = flip foldMap zf $ \case
    Binding x -> B0 :< x
    _ -> B0

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
