{-# OPTIONS_GHC -Wincomplete-patterns #-}
module Elaboration.Monad where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

import Actor (ActorVar, AContextStack, AProtocol, Channel)
import Bwd
import Concrete.Base
import Location (HasGetRange(..), Range, WithRange (..))
import Syntax (SyntaxCat, SyntaxDesc, VSyntaxDesc'(..), VSyntaxDesc, SyntaxTable, wildcard)
import qualified Syntax
import Thin (Selable(..), DB (..), CdB (..))
import Term.Base (Tm(..), atom)
import Utils

------------------------------------------------------------------------------
-- Elaboration Monad

data ElabState = ElabState
  { channelStates :: ChannelStates
  , actvarStates  :: ActvarStates
  , syntaxCats    :: SyntaxTable
  , warnings      :: Bwd Warning
  }

type ChannelState = (Direction, [Turn], AProtocol)
type ChannelStates = Map Channel ChannelState

type ActvarStates = Map ActorVar (Bwd Usage)

data Usage
  = SentAsSubject Range
  | SentInOutput Range
  | LookedUp Range
  | Scrutinised Range
  | Compared Range
  | Constrained Range
  | LetBound Range
  | Pushed Range
  | SuccessfullyLookedUp Range
  | DontLog
 deriving Show

wasScrutinised :: Foldable t => t Usage -> Bool
wasScrutinised = any $ \case
  Scrutinised _ -> True
  SentAsSubject _ -> True
  SuccessfullyLookedUp _ -> True
  _ -> False

data Direction = Rootwards
               | Leafwards
  deriving (Eq, Show)

initElabState :: ElabState
initElabState = ElabState Map.empty Map.empty Map.empty B0

newtype Elab a = Elab
  { runElab :: StateT ElabState
               (ReaderT Context
               (WriterT All       -- Can we win?
               (Either Complaint)))
               a }
  deriving ( Functor, Applicative, Monad
           , MonadError Complaint
           , MonadReader Context
           , MonadState ElabState
           , MonadWriter All)

evalElab :: Elab a -> Either Complaint a
evalElab = fmap fst
         . runWriterT
         . (`runReaderT` initContext)
         . (`evalStateT` initElabState)
         . runElab

------------------------------------------------------------------------------
-- Partial Info

data Info a = Unknown | Known a | Inconsistent
  deriving (Show, Eq, Functor)

instance Applicative Info where
  pure = Known
  (<*>) = ap

instance Monad Info where
  Unknown >>= f = Unknown
  Known a >>= f = f a
  Inconsistent >>= f = Inconsistent

instance Eq a => Semigroup (Info a) where
  Unknown <> y = y
  x <> Unknown = x
  Known x <> Known y | x == y = Known x
  _ <> _ = Inconsistent

instance Eq a => Monoid (Info a) where
  mempty = Unknown

infoExpand :: SyntaxTable -> SyntaxDesc -> Info VSyntaxDesc
infoExpand table s = case Syntax.expand table s of
  Nothing -> Inconsistent
  Just VWildcard -> Unknown
  Just a -> Known a

fromInfo :: Range -> Info SyntaxDesc -> Elab SyntaxDesc
fromInfo r Unknown = pure (atom "Wildcard" 0)
fromInfo r (Known desc) = pure desc
-- I believe this last case is currently unreachable because this
-- may only arise from a call to (<>) and this is only used in two
-- places:
-- 1. `addHint` (and if we had a clash, that'd be a shadowing error)
-- 2. `compatibleInfos` where the error is handled locally
fromInfo r Inconsistent = throwError (InconsistentSyntaxDesc r)

compatibleInfos :: Range -> Info SyntaxDesc -> Info SyntaxDesc -> Elab (Info SyntaxDesc)
compatibleInfos r desc desc' = do
  table <- gets syntaxCats
  let de = infoExpand table =<< desc
  let de' = infoExpand table =<< desc'
  case de <> de' of
    Inconsistent -> throwError (IncompatibleSyntaxInfos r desc desc')
    d -> pure $ case (desc, desc') of
      (Known (CdB (A _) _), _) -> desc
      (_, Known (CdB (A _) _)) -> desc'
      _ -> Syntax.contract <$> d

------------------------------------------------------------------------------
-- Context

type ObjVar = (String, Info SyntaxDesc)
type ObjVars = Bwd ObjVar

data Provenance = Parent | Pattern
  deriving (Show)

data IsSubject' a = IsSubject a | IsNotSubject
  deriving (Show, Functor)

type IsSubject = IsSubject' Provenance

type instance SCRUTINEEVAR Elaboration = (IsSubject, SyntaxDesc)
type instance STACK Elaboration = SyntaxDesc
type instance TERM Elaboration = ()
type instance LOOKEDUP Elaboration = String

type EScrutinee = SCRUTINEE Elaboration

isSubjectFree :: EScrutinee -> Bool
isSubjectFree = \case
  Nil{} -> True
  Lookup{} -> True
  Compare{} -> True
  Pair _ p q -> isSubjectFree p && isSubjectFree q
  ActorVar _ (IsSubject{}, _) -> False
  ActorVar _ (IsNotSubject, _) -> True

data Kind
  = ActVar IsSubject (Info SyntaxDesc) ObjVars
  | AChannel ObjVars
  | AJudgement ExtractMode AProtocol
  | AStack AContextStack
  deriving (Show)

type Decls = Bwd (String, Kind)
data Context = Context
  { objVars      :: ObjVars
  , declarations :: Decls
  , operators    :: Map String (SyntaxDesc, [SyntaxDesc])
  , location     :: Bwd Turn
  , binderHints  :: Hints
  , elabMode     :: ElabMode
  } deriving (Show)

type Hints = Map String (Info SyntaxDesc)

data ElabMode = Definition | Execution
              deriving (Eq, Show)

initContext :: Context
initContext = Context
  { objVars = B0
  , declarations = B0
  , operators = Map.fromList [("app", (wildcard,[wildcard]))]
  , location = B0
  , binderHints = Map.empty
  , elabMode = Definition
  }

declareObjVar :: ObjVar -> Context -> Context
declareObjVar x ctx = ctx { objVars = objVars ctx :< x }

setObjVars :: ObjVars -> Context -> Context
setObjVars ovs ctx = ctx { objVars = ovs }

instance Selable Context where
  th ^? ctxt = ctxt { objVars = th ^? objVars ctxt }

declare :: Binder String -> Kind -> Context -> Context
declare Unused k ctx = ctx
declare (Used x) k ctx = ctx { declarations = declarations ctx :< (x, k) }

setDecls :: Decls -> Context -> Context
setDecls ds ctx = ctx { declarations = ds }

------------------------------------------------------------------------------
-- Hierarchical path names generation

data Turn = West | East
  deriving (Show, Eq)

getName :: Elab [Turn]
getName = do
  loc <- asks location
  pure (loc <>> [])

turn :: Turn -> Context -> Context
turn t ds = ds { location = location ds :< t }

------------------------------------------------------------------------------
-- Hints

setHints :: Hints -> Context -> Context
setHints hs ctx = ctx { binderHints = hs }

addHint :: String -> Info SyntaxDesc -> Context -> Context
addHint str cat ctx =
  let hints = binderHints ctx
      hints' = case Map.lookup str hints of
                 Nothing -> Map.insert str cat hints
                 Just cat' -> Map.insert str (cat <> cat') hints
  in ctx { binderHints = hints' }

getHint :: String -> Elab (Info SyntaxDesc)
getHint str = do
  hints <- asks binderHints
  pure $ fromMaybe Unknown $ Map.lookup str hints

------------------------------------------------------------------------------
-- Warnings

data Warning
  = UnreachableClause Range RawP
  | MissingClauses Range (NonEmpty RawP)
  -- Subject tracking
  | SentSubjectNotASubjectVar Range Raw
  | RecvSubjectNotScrutinised Range Channel (Binder String)
  | PatternSubjectNotScrutinised Range String
  | UnderscoreOnSubject Range
  | InconsistentScrutinisation Range

instance HasGetRange Warning where
  getRange = \case
    UnreachableClause r _ -> r
    MissingClauses r _ -> r
    -- Subject analysis
    SentSubjectNotASubjectVar r _ -> r
    RecvSubjectNotScrutinised r _ _ -> r
    PatternSubjectNotScrutinised r _ -> r
    UnderscoreOnSubject r -> r
    InconsistentScrutinisation r -> r

raiseWarning :: Warning -> Elab ()
raiseWarning w = do
  modify (\ r -> r { warnings = warnings r :< w })

------------------------------------------------------------------------------
-- Errors

during :: (Complaint -> Complaint) -> Elab a -> Elab a
during f ma = ma `catchError` (throwError . f)

data Complaint
  -- scope
  = OutOfScope Range Variable
  | MetaScopeTooBig Range Variable ObjVars ObjVars
  | VariableShadowing Range Variable
  | EmptyContext Range
  | NotTopVariable Range Variable Variable
  | IncompatibleChannelScopes Range ObjVars ObjVars
  -- kinding
  | NotAValidTermVariable Range Variable Kind
  | NotAValidPatternVariable Range Variable Kind
  | NotAValidJudgement Range Variable (Maybe Kind)
  | NotAValidStack Range Variable (Maybe Kind)
  | NotAValidChannel Range Variable (Maybe Kind)
  | NotAValidBoundVar Range Variable
  | NotAValidActorVar Range Variable
  | NotAValidOperator Range String
  -- protocol
  | InvalidSend Range Channel Raw
  | InvalidRecv Range Channel (Binder String)
  | NonLinearChannelUse Range Channel
  | UnfinishedProtocol Range Channel AProtocol
  | InconsistentCommunication Range
  | DoomedBranchCommunicated Range CActor
  | ProtocolsNotDual Range AProtocol AProtocol
  | IncompatibleModes Range (Mode, SyntaxDesc) (Mode, SyntaxDesc)
  | WrongDirection Range (Mode, SyntaxDesc) Ordering (Mode, SyntaxDesc)
  -- syntaxes
  | AlreadyDeclaredSyntaxCat Range SyntaxCat
  -- syntaxdesc validation
  | InconsistentSyntaxDesc Range
  | InvalidSyntaxDesc Range SyntaxDesc
  | IncompatibleSyntaxInfos Range (Info SyntaxDesc) (Info SyntaxDesc)
  | IncompatibleSyntaxDescs Range SyntaxDesc SyntaxDesc
  | GotBarredAtom Range String [String]
  | ExpectedNilGot Range String
  | ExpectedEnumGot Range [String] String
  | ExpectedTagGot Range [String] String
  | ExpectedANilGot Range Raw
  | ExpectedANilPGot Range RawP
  | ExpectedAConsGot Range Raw
  | ExpectedAConsPGot Range RawP
  | SyntaxError Range SyntaxDesc Raw
  | SyntaxPError Range SyntaxDesc RawP
  | ExpectedAnOperator Range Raw
  | ExpectedAnEmptyListGot Range String [SyntaxDesc]
  -- contextual info
  -- shouldn't contain ranges because there should be a more precise one
  -- on the decorated complaint
  | SendTermElaboration Channel Raw Complaint
  | MatchElaboration CScrutinee Complaint
  | MatchBranchElaboration RawP Complaint
  | ConstrainTermElaboration Raw Complaint
  | ConstrainSyntaxCatGuess Raw Raw Complaint
  | FreshMetaElaboration Complaint
  | UnderElaboration Complaint
  | RecvMetaElaboration Channel Complaint
  | PushTermElaboration Raw Complaint
  | LookupVarElaboration Variable Complaint
  | DeclJElaboration Variable Complaint
  | DefnJElaboration Variable Complaint
  | ExecElaboration Complaint
  | DeclaringSyntaxCat SyntaxCat Complaint
  | SubstitutionElaboration (Bwd SbstC) Complaint
  | PatternVariableElaboration Variable Complaint
  | TermVariableElaboration Variable Complaint
  | ProtocolElaboration CProtocol Complaint
  | ConnectElaboration Variable Variable Complaint
  | CompareTermElaboration Raw Complaint
  | MatchScrutineeElaboration CScrutinee Complaint
  | CompareSyntaxCatGuess Raw Raw Complaint
  deriving (Show)

instance HasGetRange Complaint where
  getRange = \case
    OutOfScope r _ -> r
    MetaScopeTooBig r _ _ _ -> r
    VariableShadowing r _ -> r
    EmptyContext r -> r
    NotTopVariable r _ _ -> r
    IncompatibleChannelScopes r _ _ -> r
  -- kinding
    NotAValidTermVariable r _ _ -> r
    NotAValidPatternVariable r _ _ -> r
    NotAValidJudgement r _ _ -> r
    NotAValidStack r _ _ -> r
    NotAValidChannel r _ _ -> r
    NotAValidBoundVar r _ -> r
    NotAValidActorVar r _ -> r
    NotAValidOperator r _ -> r
  -- protocol
    InvalidSend r _ _ -> r
    InvalidRecv r _ _ -> r
    NonLinearChannelUse r _ -> r
    UnfinishedProtocol r _ _ -> r
    InconsistentCommunication r -> r
    DoomedBranchCommunicated r _ -> r
    ProtocolsNotDual r _ _ -> r
    IncompatibleModes r _ _ -> r
    WrongDirection r _ _ _ -> r
  -- syntaxes
    AlreadyDeclaredSyntaxCat r _ -> r
  -- syntaxdesc validation
    InconsistentSyntaxDesc r -> r
    InvalidSyntaxDesc r _ -> r
    IncompatibleSyntaxInfos r _ _ -> r
    IncompatibleSyntaxDescs r _ _ -> r
    GotBarredAtom r _ _ -> r
    ExpectedNilGot r _ -> r
    ExpectedEnumGot r _ _ -> r
    ExpectedTagGot r _ _ -> r
    ExpectedANilGot r _ -> r
    ExpectedANilPGot r _ -> r
    ExpectedAConsGot r _ -> r
    ExpectedAConsPGot r _ -> r
    SyntaxError r _ _ -> r
    SyntaxPError r _ _ -> r
    ExpectedAnOperator r _ -> r
    ExpectedAnEmptyListGot r _ _ -> r
  -- contextual info
  -- shouldn't contain ranges because there should be a more precise one
  -- on the decorated complaint
    SendTermElaboration _ _ c -> getRange c
    MatchElaboration _ c -> getRange c
    MatchBranchElaboration _ c -> getRange c
    ConstrainTermElaboration _ c -> getRange c
    ConstrainSyntaxCatGuess _ _ c -> getRange c
    FreshMetaElaboration c -> getRange c
    UnderElaboration c -> getRange c
    RecvMetaElaboration _ c -> getRange c
    PushTermElaboration _ c -> getRange c
    LookupVarElaboration _ c -> getRange c
    DeclJElaboration _ c -> getRange c
    DefnJElaboration _ c -> getRange c
    ExecElaboration c -> getRange c
    DeclaringSyntaxCat _ c -> getRange c
    SubstitutionElaboration _ c -> getRange c
    PatternVariableElaboration _ c -> getRange c
    TermVariableElaboration _ c -> getRange c
    ProtocolElaboration _ c -> getRange c
    ConnectElaboration _ _ c -> getRange c
    CompareTermElaboration _ c -> getRange c
    MatchScrutineeElaboration _ c -> getRange c
    CompareSyntaxCatGuess _ _ c -> getRange c

------------------------------------------------------------------------------
-- Syntaxes

declareSyntax :: WithRange SyntaxCat -> SyntaxDesc -> Elab ()
declareSyntax (WithRange r cat) desc = do
  st <- get
  whenJust (Map.lookup cat (syntaxCats st)) $ \ _ ->
    throwError (AlreadyDeclaredSyntaxCat r cat)
  put (st { syntaxCats = Map.insert cat desc (syntaxCats st) })

withSyntax :: SyntaxDesc -> Elab a -> Elab a
withSyntax desc ma = do
  st <- get
  put $ st { syntaxCats = Map.singleton "Syntax" desc }
  a <- ma
  put $ st { syntaxCats = syntaxCats st }
  pure a

------------------------------------------------------------------------------
-- Channels

channelLookup :: Channel -> ElabState -> Maybe ChannelState
channelLookup ch = Map.lookup ch . channelStates

channelInsert :: Channel -> ChannelState -> ElabState -> ElabState
channelInsert ch x st = st { channelStates = Map.insert ch x (channelStates st) }

channelDelete :: Channel -> ElabState -> ElabState
channelDelete ch st = st { channelStates = Map.delete ch (channelStates st) }

------------------------------------------------------------------------------
-- Variable lookup

resolve :: Variable -> Elab (Maybe (Either Kind (Info SyntaxDesc, DB)))
resolve (Variable r x) = do
  ctx <- ask
  let ds  = declarations ctx
  let ovs = objVars ctx
  case focusBy (\ (y, k) -> k <$ guard (x == y)) ds of
    Just (_, k, _) -> pure (Just $ Left k)
    _ -> case focusBy (\ (y, desc) -> desc <$ guard (x == y)) ovs of
      Just (xz, desc, xs) -> pure (Just $ Right (desc, DB $ length xs))
      Nothing -> pure Nothing

------------------------------------------------------------------------------
-- Subject usage logging

logUsage :: ActorVar -> Usage -> Elab ()
logUsage _ DontLog = pure ()
logUsage var usage = do
  em <- asks elabMode
  when (em == Definition) $
    modify (\st -> st { actvarStates = Map.alter (Just . (:< usage) . fromMaybe B0) var (actvarStates st) })

setElabMode :: ElabMode -> Context -> Context
setElabMode em ctx = ctx { elabMode = em }
