{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}

module Machine.Base where

import qualified Data.Map as Map
import Data.Maybe

import Actor
import Bwd
import Format
import Options
import Term
import Thin
import Concrete.Base (ExtractMode, isWin, ACTOR)
import Syntax (SyntaxDesc)

newtype Date = Date Int
  deriving (Show, Eq, Ord, Num)

-- | i stores extra information, typically a naming
data StoreF i = Store
  { solutions :: Map.Map Meta (i, Term)
  , today :: Date
  } deriving (Show)

initStore :: StoreF i
initStore = Store Map.empty 0

tick :: StoreF i -> StoreF i
tick st@Store{..} = st { today = today + 1 }

updateStore :: Meta -> i -> Term -> StoreF i -> StoreF i
updateStore m i t st@Store{..} = tick $ st
  { solutions = Map.insert m (i, t) solutions }

headUp :: StoreF i -> Term -> Term
headUp store term
  | m :$: sg <- expand term
  , Just (_, t) <- Map.lookup m (solutions store)
  = headUp store (t //^ sg)
  | otherwise = term

class Instantiable t where
  type Instantiated t
  instantiate :: StoreF i -> t -> Instantiated t

class Instantiable1 t where
  type Instantiated1 t :: * -> *
  instantiate1 :: StoreF i -> t a -> Instantiated1 t a

instance Instantiable Term where
  type Instantiated Term = Term
  instantiate store term = case expand term of
    VX{}     -> term
    AX{}     -> term
    s :%: t  -> instantiate store s % instantiate store t
    x :.: b  -> x \\ instantiate store b
    m :$: sg -> case Map.lookup m (solutions store) of
      Nothing -> m $: sg -- TODO: instantiate sg
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
  , judgeName :: JudgementForm
  , judgeProtocol :: AProtocol
  , extractionMode :: ExtractMode
  , traffic :: Bwd Term
  } deriving (Show)

-- Do NOT reorder arguments: derived Ord needs to be this way
data Status
  = New
  | StuckOn Date
  | Done
  deriving (Show, Eq, Ord)


isDone :: Status -> Bool
isDone Done = True
isDone _ = False

data Frame
  = Rules JudgementForm AProtocol (Channel, AActor)
  | LeftBranch Hole (Process () Status [])
  | RightBranch (Process () Status []) Hole
  | Spawnee (Interface Hole (Process () Status []))
  | Spawner (Interface (Process () Status []) Hole)
  | Sent Channel ([String], Term)
  | Pushed Stack (DB, SyntaxDesc, Term)
  | Binding String
  | UnificationProblem Date Term Term
  | Noted
  deriving (Show)

status :: [Frame] -> ACTOR ph -> Date -> Status
status fs a d = if foldr (\ f acc -> acc && hasWon f) (isWin a) fs
                then Done
                else StuckOn d
  where

  hasWon :: Frame -> Bool
  hasWon Rules{} = True
  hasWon (LeftBranch Hole p)  = isDone (store p)
  hasWon (RightBranch p Hole) = isDone (store p)
  hasWon (Spawnee i) = isDone (store $ snd $ spawner i)
  hasWon (Spawner i) = isDone (store $ fst $ spawnee i)
  hasWon (Sent ch t) = False
  hasWon (Pushed s tm) = True
  hasWon (Binding s) = True
  hasWon (UnificationProblem d t t') = False
  hasWon Noted = True



data Process l s t
  = Process
  { options :: Options
  , stack   :: t Frame -- Stack frames ahead of or behind us
  , root    :: Root    -- Name supply
  , env     :: Env     -- definitions in scope
  , store   :: s       -- Definitions we know for metas (or not)
  , actor   :: AActor  -- The thing we are
  , logs    :: l
  }

tracing :: Process log s t -> [MachineStep]
tracing = fromMaybe [] . tracingOption . options

instance (Show s, Show (t Frame)) => Show (Process log s t) where
  show (Process opts stack root env store actor _) =
   unwords ["Process ", show opts, show stack, show root, show env, show store, show actor]
