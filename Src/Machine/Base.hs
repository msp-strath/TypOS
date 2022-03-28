{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}

module Machine.Base where

import qualified Data.Map as Map

import Actor
import Format
import Term
import Thin

newtype Date = Date Int
  deriving (Show, Eq, Ord, Num)

-- | i stores extra information, typically a naming
data StoreF i = Store
  { solutions :: Map.Map Meta (i, Term)
  , today :: Date
  } deriving (Show)

initStore :: StoreF i
initStore = Store Map.empty 0

updateStore :: Meta -> i -> Term -> StoreF i -> StoreF i
updateStore m i t (Store{..}) = Store
  { solutions = Map.insert m (i, t) solutions
  , today = today + 1 }

headUp :: StoreF i -> Term -> Term
headUp store term
  | m :$: sg <- expand term
  , Just (_, t) <- Map.lookup m (solutions store)
  = headUp store (t //^ sg)
  | otherwise = term

class Instantiable t where
  type Instantiated t
  instantiate :: StoreF i -> t -> Instantiated t

instance Instantiable Term where
  type Instantiated Term = Term
  instantiate store term = case expand term of
    VX{}     -> term
    AX{}     -> term
    s :%: t  -> instantiate store s % instantiate store t
    x :.: b  -> x \\ instantiate store b
    m :$: sg -> case Map.lookup m (solutions store) of
      Nothing -> m $: sg
      Just (_, tm) -> instantiate store (tm //^ sg)

instance (Show t, Instantiable t, Instantiated t ~ t) =>
  Instantiable (Format Directive dbg t) where
  type Instantiated (Format Directive dbg t) = Format () dbg t
  instantiate store = \case
    TermPart Instantiate t -> TermPart () (instantiate store t)
    TermPart Raw t -> TermPart () t
    TermPart ShowT t -> StringPart (show t)
    DebugPart dbg  -> DebugPart dbg
    StringPart str -> StringPart str

instance Instantiable t => Instantiable [t] where
  type Instantiated [t] = [Instantiated t]
  instantiate store = map (instantiate store)

data Hole = Hole deriving Show

data Interface c p = Interface
  { spawnee :: (c, Channel)
  , spawner :: ((Channel, [String]), p)
  } deriving (Show)

-- Do NOT reorder arguments: derived Ord needs to be this way
data Status
  = New
  | StuckOn Date
--  | Done
  deriving (Show, Eq, Ord)

data Frame
  = Rules JudgementForm (Channel, AActor)
  | LeftBranch Hole (Process Status [])
  | RightBranch (Process Status []) Hole
  | Spawnee (Interface Hole (Process Status []))
  | Spawner (Interface (Process Status []) Hole)
  | Sent Channel ([String], Term)
  | Connected Channel Channel
  | Pushed JudgementForm (DB, Term)
  | Binding String
  | UnificationProblem Date Term Term
  deriving (Show)

data MachineStep
  = MachineRecv
  | MachineSend
  | MachineExec
  | MachineMove
  | MachineUnify
  | MachineBreak
  deriving (Eq, Show, Enum, Bounded)

data Process s t
  = Process
  { tracing :: [MachineStep]
  , stack   :: t Frame -- Stack frames ahead of or behind us
  , root    :: Root    -- Name supply
  , env     :: Env     -- definitions in scope
  , store   :: s       -- Definitions we know for metas (or not)
  , actor   :: AActor  -- The thing we are
  , judgementform :: JudgementForm -- who we are
  }

deriving instance (Show s, Show (t Frame)) => Show (Process s t)
