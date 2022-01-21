{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}

module Machine.Base where

import qualified Data.Map as Map

import Term
import Actor

newtype Date = Date Int
  deriving (Show, Eq, Ord, Num)

data Store = Store
  { solutions :: Map.Map Meta Term
  , today :: Date
  }

initStore :: Store
initStore = Store Map.empty 0

updateStore :: Meta -> Term -> Store -> Store
updateStore m t (Store{..}) = Store { solutions = Map.insert m t solutions, today = today + 1 }

data Hole = Hole deriving Show

data Frame
  = Rules JudgementForm (Channel, Actor)
  | RulePatch JudgementForm MatchLabel Alias Env Actor
  | LeftBranch Hole (Process Date [])
  | RightBranch (Process Date []) Hole
  | Spawnee (Hole, Channel) (Channel, Process Date [])
  | Spawner (Process Date [], Channel) (Channel, Hole)
  | Sent Channel Term
  | Binding String
  | UnificationProblem Date Term Term
  deriving (Show)

data Process s t
  = Process
  { stack :: t Frame -- Stack frames ahead of or behind us
  , root  :: Root    -- Name supply
  , env   :: Env     -- definitions in scope
  , store :: s       -- Definitions we know for metas (or not)
  , actor :: Actor   -- The thing we are
  }

deriving instance (Show s, Show (t Frame)) => Show (Process s t)
