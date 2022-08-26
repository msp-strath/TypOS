{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}

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
import Concrete.Base (ExtractMode, ACTOR (..), Operator(..))
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

data HeadUpData = forall i. HeadUpData
  { opTable :: Operator -> Clause
  , metaStore :: StoreF i
  }

mkOpTable :: Bwd Frame -> Operator -> Clause
mkOpTable _ (Operator "app") = appClause
mkOpTable _ (Operator "when") = whenClause
mkOpTable fs op = flip foldMap fs $ \case
  Extended op' cl | op == op' -> cl
  _ -> mempty

-- Expanding the term using the information currently available:
-- + meta solutions
-- + operator clauses
headUp :: HeadUpData -> Term -> Term
headUp dat@HeadUpData{..} term = case expand term of
  m :$: sg | Just (_, Just t) <- Map.lookup m (solutions metaStore)
    -> headUp dat (t //^ sg)
  t :-: o -> case expand o of
    AX op i -> operate (Operator op) (t, [])
    o@(CdB (A op) th :%: wargs) ->
      case asList (\ ps -> pure $ operate (Operator op) (t, ps)) wargs of
        Nothing -> contract (t :-: contract o)
        Just t -> t
    o -> contract (t :-: contract o)
  _ -> term

  where

  operate :: Operator -> (Term, [Term]) -> Term
  operate op tps = case runClause (opTable op) (headUp dat) tps of
    Left (t, []) -> contract (t :-: contract (AX (getOperator op) (scope term)))
    Left (t, ps) -> contract (t :-: (getOperator op #%+ ps))
    Right t -> headUp dat t


compareUp :: HeadUpData -> Term -> Term -> Maybe Ordering
compareUp dat s t = case (expand (headUp dat s), expand (headUp dat t)) of
  (VX i _, VX j _) -> pure (compare i j)
  (AX a _, AX b _) -> pure (compare a b)
  (p :%: q, a :%:b) -> do
    c1 <- compareUp dat p a
    case c1 of
      EQ -> compareUp dat q b
      _ -> pure c1
  (x :.: b, y :.: c) -> compareUp dat b c
  (m :$: sg, n :$: sg') | m == n, Just EQ <- comparesUp dat sg sg' -> pure EQ
  (m :$: sg, _) -> Nothing
  (_, m :$: sg) -> Nothing
  (VX{}, _) -> pure LT
  (_, VX{}) -> pure GT
  (AX{}, _) -> pure LT
  (_, AX{}) -> pure GT
  ((:%:){}, _) -> pure LT
  (_, (:%:){}) -> pure GT

comparesUp :: HeadUpData -> Subst -> Subst -> Maybe Ordering
comparesUp dat sg sg' = compareUp dat (toTerm sg) (toTerm sg') where

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

newtype Clause = Clause { runClause
  :: (Term -> Term) -- head normaliser
  -> (Term, [Term]) -- object & parameters
  -> Either (Term, [Term]) Term }

instance Semigroup Clause where
  (<>) = mappend

instance Monoid Clause where
  mempty = Clause $ const Left
  mappend cl1 cl2 = Clause $ \ hd ops -> case runClause cl2 hd ops of
    Left ops -> runClause cl1 hd ops
    Right t -> Right t

instance Show Clause where
  show _ = "<fun>"

appClause :: Clause
appClause = Clause $ \ hd (t, args) ->
  case args of
    [arg] -> case expand (hd t) of
      x :.: b -> Right (b //^ topSbst x arg)
      t -> Left (contract t, args)
    _ -> Left (t, args)

whenClause :: Clause
whenClause = Clause $ \ hd (t, args) -> case args of
  [arg] -> case expand (hd arg) of
    AX "True" _ -> Right t
    arg -> Left (t, [contract arg])
  _ ->  Left (t, args)

data Frame
  = Rules JudgementForm AProtocol (Channel, AActor)
  | LeftBranch Hole (Process () Status [])
  | RightBranch (Process () Status []) Hole
  | Spawnee (Interface Hole (Process () Status []))
  | Spawner (Interface (Process () Status []) Hole)
  | Sent Channel ([String], Term)
  | Pushed Stack (DB, SyntaxDesc, Term)
  | Extended Operator Clause
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
  , env     :: Env     -- Definitions in scope
  , store   :: s       -- Definitions we know for metas (or not)
  , actor   :: AActor  -- The thing we are
  , logs    :: l       -- The shots of the VM's state we have taken
  }

tracing :: Process log s t -> [MachineStep]
tracing = fromMaybe [] . tracingOption . options

instance (Show s, Show (t Frame)) => Show (Process log s t) where
  show (Process opts stack root env store actor _) =
   unwords ["Process ", show opts, show stack, show root, show env, show store, show actor]
