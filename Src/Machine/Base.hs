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
import Concrete.Base (ExtractMode, ACTOR (..))
import Syntax (SyntaxDesc)
import Control.Monad (join)

newtype Date = Date Int
  deriving (Show, Eq, Ord, Num)

-- | i stores extra information, typically a naming
data StoreF i = Store
  { solutions :: Map.Map Meta (i, Maybe Term)
  , today :: Date
  } deriving (Show)

initStore :: StoreF i
initStore = Store Map.empty 0

tick :: StoreF i -> StoreF i
tick st@Store{..} = st { today = today + 1 }

declareMeta :: Meta -> i -> StoreF i -> StoreF i
declareMeta m i st@Store{..} = st
  { solutions = Map.insert m (i, Nothing) solutions }

updateStore :: Meta -> Term -> StoreF i -> StoreF i
updateStore m t st@Store{..} = tick $ st
  { solutions = Map.adjust (Just t <$) m solutions }

headUp :: StoreF i -> Term -> Term
headUp store term = case expand term of
  m :$: sg | Just (_, Just t) <- Map.lookup m (solutions store)
    -> headUp store (t //^ sg)
  t :-: o -> case expand o of
    CdB (A "app") th :%: warg -> case expand (headUp store warg) of
      arg :%: _ -> case expand (headUp store t) of
        x :.: b -> headUp store (b //^ topSbst x arg)
        t -> contract (contract t :-: ("app" #%+ [arg]))
    o -> contract (t :-: contract o)
  _ -> term

compareUp :: StoreF i -> Term -> Term -> Maybe Ordering
compareUp store s t = case (expand (headUp store s), expand (headUp store t)) of
  (VX i _, VX j _) -> pure (compare i j)
  (AX a _, AX b _) -> pure (compare a b)
  (p :%: q, a :%:b) -> do
    c1 <- compareUp store p a
    case c1 of
      EQ -> compareUp store q b
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

class Instantiable1 t where
  type Instantiated1 t :: * -> *
  instantiate1 :: StoreF i -> t a -> Instantiated1 t a

instance Instantiable Term where
  type Instantiated Term = Term
  instantiate store term = case expand term of
    VX{}     -> term
    AX{}     -> term
    s :%: t  -> instantiate store s % instantiate store t
    s :-: t  -> contract (instantiate store s :-: instantiate store t)
    x :.: b  -> x \\ instantiate store b
    m :$: sg -> case join $ fmap snd $ Map.lookup m (solutions store) of
      Nothing -> m $: sg -- TODO: instantiate sg
      Just tm -> instantiate store (tm //^ sg)

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
  | Dead
  | Done
  deriving (Show, Eq, Ord)

instance Semigroup Status where
  (<>) = min

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
status fs a d = minimum (actorStatus a : map frameStatus fs)

  where

  actorStatus :: ACTOR ph -> Status
  actorStatus Win{} = Done
  actorStatus Fail{} = Dead
  actorStatus _ = StuckOn d

  frameStatus :: Frame -> Status
  frameStatus Rules{} = Done
  frameStatus (LeftBranch Hole p) = store p
  frameStatus (RightBranch p Hole) = store p
  frameStatus (Spawnee i) = store (snd $ spawner i)
  frameStatus (Spawner i) = store (fst $ spawnee i)
  frameStatus Sent{} = StuckOn d
  frameStatus Pushed{} = Done
  frameStatus Binding{} = Done
  frameStatus UnificationProblem{} = StuckOn d
  frameStatus Noted = Done

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
