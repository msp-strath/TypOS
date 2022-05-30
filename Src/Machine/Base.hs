{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}

module Machine.Base where

import qualified Data.Map as Map
import Data.Maybe

import Actor
import Bwd
import Format
import Options
import Term
import qualified Term.Substitution as Substitution
import Thin
import Concrete.Base (ExtractMode)
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

compareUp :: StoreF i -> Term -> Term -> Maybe Ordering
compareUp store s t = case (expand (headUp store s), expand (headUp store t)) of
  (VX i _, VX j _) -> pure (compare i j)
  (AX a _, AX b _) -> pure (compare a b)
  (p :%: q, a :%:b) -> do
    c1 <- compareUp store p a
    c2 <- compareUp store q b
    case c1 of
      EQ -> pure c2
      _ -> pure c1
  (x :.: b, y :.: c) -> compareUp store b c
  (m :$: sg, n :$: sg') | m == n, Just EQ <- comparesUp store sg sg' -> pure EQ
  (m :$: sg, _) -> Nothing
  (_, m :$: sg) -> Nothing
  (VX{}, _) -> pure LT
  (_, VX{}) -> pure GT
  (AX{}, _) -> pure LT
  (_, AX{}) -> pure GT
  ((:%:){}, _) -> pure LT
  (_, (:%:){}) -> pure GT

comparesUp :: StoreF i -> Subst -> Subst -> Maybe Ordering
comparesUp store sg sg' = compareUp store (toTerm sg) (toTerm sg') where

  toTerm (CdB sg th) = ("Hack", bigEnd th) #% (Substitution.expand sg th <>> [])

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
--  | Done
  deriving (Show, Eq, Ord)

data Frame
  = Rules JudgementForm AProtocol (Channel, AActor)
  | LeftBranch Hole (Process Status [])
  | RightBranch (Process Status []) Hole
  | Spawnee (Interface Hole (Process Status []))
  | Spawner (Interface (Process Status []) Hole)
  | Sent Channel ([String], Term)
  | Pushed Stack (DB, SyntaxDesc, Term)
  | Binding String
  | UnificationProblem Date Term Term
  | Noted
  deriving (Show)

data Process s t
  = Process
  { options :: Options
  , stack   :: t Frame -- Stack frames ahead of or behind us
  , root    :: Root    -- Name supply
  , env     :: Env     -- definitions in scope
  , store   :: s       -- Definitions we know for metas (or not)
  , actor   :: AActor  -- The thing we are
  }

tracing :: Process s t -> [MachineStep]
tracing = fromMaybe [] . tracingOption . options

deriving instance (Show s, Show (t Frame)) => Show (Process s t)
