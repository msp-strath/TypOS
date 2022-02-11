module Machine.Display where

import Control.Monad.State

import qualified Data.Map as Map

import Bwd
import Display
import Term
import Thin
import ANSI
import Actor
import Actor.Display()
import Machine.Base

instance Display Date where
  display na (Date i) = show i

instance Display Frame where
  display na = \case
    Rules jd (ch, a) -> jd ++ " |-@" ++ show ch ++ " {}" -- ++ pdisplay na a
    RulePatch jd ml i env a -> jd ++ display initNaming ml ++ " |- +" ++ " " ++ show i ++ " -> {}"{- ++ display na env ++ " " ++ pdisplay na a -}
    LeftBranch Hole p -> "<> | " ++ display na p
    RightBranch p Hole -> display na p ++ " | <>"
    Spawnee (Hole, lch) (rch, p) -> "<> @ " ++ show lch ++ " | " ++ show rch ++ " @ " ++ display na p
    Spawner (p, lch) (rch, Hole) -> display na p ++ " @ " ++ show lch ++ " | " ++ show rch ++ " @ <>"
    Sent ch t -> withANSI [SetColour Foreground Blue, SetWeight Bold] $ "!" ++ show ch ++ ". " ++ display na t
    Binding x -> withANSI [SetColour Foreground Yellow, SetWeight Bold]
                 $ "\\" ++ x ++ ". "
    UnificationProblem date s t -> withANSI [SetColour Background Red] (display na s ++ " ~?[" ++ display na date ++ "] " ++ display na t)

instance (Traversable t, Collapse t, Display s) => Display (Process s t) where
  display na p = let (fs', store', env', a') = displayProcess' na p in
     concat ["(", collapse fs', " ", store', " ", env', " ", a', ")"]

displayProcess' :: (Traversable t, Collapse t, Display s) =>
  Naming -> Process s t -> (t String, String, String, String)
displayProcess' na Process{..} =
     let (fs', na') = runState (traverse go stack) na
         store'     = display initNaming store
         env'       = pdisplay na' env
         a'         = pdisplay na' actor
     in (fs', store', case actor of Win -> ""; _ -> env', a')

    where

    go :: Frame -> State Naming String
    go f = do na <- get
              let dis = display na f
              case f of
                Binding x -> put (na `nameOn` x)
                _ -> pure ()
              pure dis

type Store = StoreF Naming

instance Display Store where
  display na st = display na (today st) ++ ": " ++
                 withANSI [SetColour Background Green
                          , SetColour Foreground Black]
                 (collapse $ map go $ Map.toList $ solutions st)
    where
    go :: (Meta, (Naming, Term)) -> String
    go (k, (na, t)) = "?" ++ show k ++ " := " ++ display na t

frnaming :: Foldable t => t Frame -> Naming
frnaming zf = (zv, ones (length zv), zv)
 where
  zv = flip foldMap zf $ \case
    Binding x -> B0 :< x
    _ -> B0
