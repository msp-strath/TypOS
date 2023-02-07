{-# LANGUAGE UndecidableInstances #-}
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

import Actor
import Bwd
import Concrete.Base
import Location (HasGetRange(..), Range, WithRange (..))
import Syntax (SyntaxCat, SyntaxDesc, VSyntaxDesc, SyntaxTable)
import Thin
import Term.Base
import Utils
import Operator
import Rules
import Info
import Pattern
import Hide
import Operator.Eval
import Options
import Semantics
------------------------------------------------------------------------------
-- Elaboration Monad

data ElabState = ElabState
  { channelStates :: ChannelStates
  , actvarStates  :: ActvarStates
  , syntaxCats    :: SyntaxTable
  , warnings      :: Bwd (WithStackTrace Warning)
  }

type ChannelState = (Direction, [Turn], [AProtocolEntry])
type ChannelStates = Map Channel ChannelState

type ActvarStates = Map ActorVar (Bwd Usage)

data Usage
  = SentAsSubject Range
  | SentInOutput Range
  | LookedUp Range
  | Scrutinised Range
  | MatchedOn Range
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

isBeingScrutinised :: Usage -> Bool
isBeingScrutinised = \case
  LookedUp _ -> True
  Scrutinised _ -> True
  SentAsSubject _ -> True
  Compared _ -> True
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
               (Either (WithStackTrace Complaint))))
               a }
  deriving ( Functor, Applicative, Monad
           , MonadReader Context
           , MonadState ElabState
           , MonadWriter All)

instance MonadError Complaint Elab where
  throwError err = do
    stk <- asks stackTrace
    Elab (throwError (WithStackTrace stk err))

  catchError ma k = Elab (catchError (runElab ma) (runElab . k . theMessage))

evalElab :: Options -> Elab a -> Either (WithStackTrace Complaint) a
evalElab opts = fmap fst
         . runWriterT
         . (`runReaderT` (initContext opts))
         . (`evalStateT` initElabState)
         . runElab

------------------------------------------------------------------------------
-- Partial Info

infoExpand :: HeadUpData' ActorMeta -> SyntaxTable -> ASemanticsDesc -> Info VSemanticsDesc
infoExpand dat table s = case Semantics.expand table dat s of
  Nothing -> Inconsistent
  Just (VWildcard _) -> Unknown
  Just a -> Known a

fromInfo :: Range -> Info ASemanticsDesc -> Elab ASemanticsDesc
fromInfo r Unknown = pure (atom "Wildcard" 0)
fromInfo r (Known desc) = pure desc
-- I believe this last case is currently unreachable because this
-- may only arise from a call to (<>) and this is only used in two
-- places:
-- 1. `addHint` (and if we had a clash, that'd be a shadowing error)
-- 2. `compatibleInfos` where the error is handled locally
fromInfo r Inconsistent = throwError (InconsistentSyntaxDesc r)

compatibleInfos :: Range -> Info ASemanticsDesc -> Info ASemanticsDesc -> Elab (Info ASemanticsDesc)
compatibleInfos r desc desc' = do
  table <- gets syntaxCats
  dat <- asks headUpData
  let de = infoExpand dat table =<< desc
  let de' = infoExpand dat table =<< desc'
  case de <> de' of
    Inconsistent -> throwError (IncompatibleSemanticsInfos r desc desc')
    d -> pure $ case (desc, desc') of
      (Known (CdB (A _) _), _) -> desc
      (_, Known (CdB (A _) _)) -> desc'
      _ -> Semantics.contract <$> d

------------------------------------------------------------------------------
-- Context

data Provenance = Parent | Pattern
  deriving (Show, Eq)

data IsSubject' a = IsSubject a | IsNotSubject
  deriving (Show, Functor, Eq)

type IsSubject = IsSubject' Provenance

type instance SCRUTINEEVAR Elaboration = ASemanticsDesc
type instance SCRUTINEETERM Elaboration = ASemanticsDesc
type instance STACK Elaboration = ASemanticsDesc
type instance TERM Elaboration = ()
type instance LOOKEDUP Elaboration = String

type EScrutinee = SCRUTINEE Elaboration

isSubjectFree :: EScrutinee -> Bool
isSubjectFree = \case
  Term{} -> True
  Lookup{} -> True
  Compare{} -> True
  Pair _ p q -> isSubjectFree p && isSubjectFree q
  SubjectVar{} -> False

data Kind
  = ActVar IsSubject ASOT
  | AChannel ObjVars
  | AJudgement ExtractMode AProtocol
  | AStack AContextStack
  deriving (Show)

type Decls = Bwd (String, Kind)
type Operators = Map String AAnOperator

-- LexicalScope = ObjVars + Macros
-- gives the meanings of things that look like variables.

-- Crucially, only the ObjVars are in scope for the abstract syntax
-- and their semantics desc is in the scope of the whole context,
-- i.e. ObjVars are ready for lookup with no further weakening.
-- Consequently, we must weaken them when we go under a binder.

type Macros = Bwd (String, Raw)
-- Macros are scope checked and expanded at def.  site but
-- not elaborated until use site. Hence, they cannot be recursive. The
-- vars that occur in a Macro are CdBVars - we have checked they are
-- in scope and if they are Macros, we have further expanded them.

data Context = Context
  { objVars      :: ObjVars
  , macros       :: Macros
  , declarations :: Decls
  , operators    :: Operators
  , location     :: Bwd Turn
  , binderHints  :: Hints
  , elabMode     :: ElabMode
  , stackTrace   :: StackTrace
  , headUpData   :: HeadUpData' ActorMeta
  } deriving (Show)

type Hints = Map String (Info ASemanticsDesc)

data Restriction = Restriction
  { support :: Bwd String
  , restriction :: Th
  }

initRestriction :: ObjVars -> Restriction
initRestriction ovs = Restriction (objVarName <$> getObjVars ovs) (ones (scopeSize ovs))

extend :: Restriction -> String -> Restriction
extend (Restriction ls th) x = Restriction (ls :< x) (th -? True)

instance Selable Restriction where
  ph ^? Restriction ls th = Restriction (ph ^? ls) (ph ^? th)

data ElabMode = Definition | Execution
              deriving (Eq, Show)

initContext :: Options -> Context
initContext opts = Context
  { objVars = ObjVars B0
  , macros = B0
  , declarations = B0
  , operators = Map.fromList
    [ ("app", AnOperator
        { opName = Operator "app"
        , objDesc = (Nothing, PP (AP "Pi")
                              $ PP (MP (am "S") (ones 0))
                                $ PP (BP (Hide "x")
                                  $ MP (am "T") (ones 1)) $ AP "")
        , paramsDesc = [(Just (am "s"), ObjVars B0 :=> (am "S" $: sbstI 0))]
        , retDesc = am "T" $: topSbst "x" (am "s" $: sbstI 0)
        })
    ]
  , location = B0
  , binderHints = Map.empty
  , elabMode = Definition
  , stackTrace = []
  , headUpData = initHeadUpData
  }
  where
    am = ActorMeta ACitizen

    initHeadUpData = HeadUpData
      { opTable = const mempty
      , metaStore = Store Map.empty Map.empty ()
      , huOptions = opts
      , huEnv = initEnv B0
      , whatIs = const Nothing
      }

-- We have already checked the name is fresh
declareObjVar :: (String, ASemanticsDesc) -> Context -> Context
declareObjVar (x, sem) ctx
  = let scp = fmap weak <$> getObjVars (objVars ctx) in
    ctx { objVars = ObjVars (scp :< ObjVar x sem) }

-- Careful! The new ovs better be a valid scope
-- i.e. all the objvars mentioned in the SemanticsDesc of
-- further vars need to be bound earlier in the telescope
setObjVars' :: ObjVars -> Context -> Context
setObjVars' ovs ctx = ctx { objVars = ovs }

-- A Γ-context Δ gives Δ variables with Γ-types

-- Thicken a context. It is the user's responsibility to
-- evict all variables whose type depends on other evicted
-- variables.
thickenObjVars :: Th             -- Δ ≤ Γ
               -> ObjVars        -- Γ-context Γ
               -> Maybe ObjVars  -- Δ-context Δ
thickenObjVars th (ObjVars ga) = ObjVars <$>
  let de = th ^? ga in
  traverse (traverse (thickenCdB th)) de

{-
setObjVars :: ObjVars -> Context -> Context
setObjVars ovs ctx = ctx { objVars = ovs }
-}

setHeadUpData :: HeadUpData' ActorMeta -> Context -> Context
setHeadUpData dat ctx = ctx { headUpData = dat}

{-
instance Selable ObjVars where
  th ^? (ObjVars ovs) = ObjVars (th ^? ovs)

instance Selable Context where
  th ^? ctxt = ctxt { objVars = th ^? objVars ctxt }
-}

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
-- Operators

setOperators :: Operators -> Context -> Context
setOperators ops ctx = ctx { operators = ops }

addOperator :: AAnOperator -> Context -> Context
addOperator op ctx =
  ctx { operators = Map.insert (getOperator . opName $ op) op (operators ctx) }

------------------------------------------------------------------------------
-- Hints

setHints :: Hints -> Context -> Context
setHints hs ctx = ctx { binderHints = hs }

addHint :: String -> Info ASemanticsDesc -> Context -> Context
addHint str cat ctx =
  let hints = binderHints ctx
      hints' = case Map.lookup str hints of
                 Nothing -> Map.insert str cat hints
                 Just cat' -> Map.insert str (cat <> cat') hints
  in ctx { binderHints = hints' }

getHint :: String -> Elab (Info ASemanticsDesc)
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
  -- Missing features
  | IgnoredIrrefutable Range RawP

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
    -- Missing features
    IgnoredIrrefutable r _ -> r

raiseWarning :: Warning -> Elab ()
raiseWarning w = do
  stk <- asks stackTrace
  modify (\ r -> r { warnings = warnings r :< WithStackTrace stk w })

------------------------------------------------------------------------------
-- Errors

during :: ContextualInfo -> Elab a -> Elab a
during c = local (\ ctx -> ctx { stackTrace = c : stackTrace ctx })

type StackTrace = [ContextualInfo]

instance HasGetRange a => HasGetRange (WithStackTrace a) where
  getRange = getRange . theMessage

data WithStackTrace a = WithStackTrace
  { theStackTrace :: StackTrace
  , theMessage :: a
  }

data ContextualInfo
  = SendTermElaboration Channel Raw
  | MatchElaboration CScrutinee
  | MatchBranchElaboration RawP
  | ConstrainTermElaboration Raw
  | ConstrainSyntaxCatGuess Raw Raw
  | FreshMetaElaboration
  | UnderElaboration
  | RecvMetaElaboration Channel
  | PushTermElaboration Raw
  | LookupVarElaboration Variable
  | DeclJElaboration Variable
  | DefnJElaboration Variable
  | ExecElaboration
  | DeclaringSyntaxCat SyntaxCat
  | SubstitutionElaboration (Bwd SbstC)
  | PatternVariableElaboration Variable
  | TermVariableElaboration Variable
  | ProtocolElaboration CProtocol
  | ConnectElaboration Variable Variable
  | CompareTermElaboration Raw
  | ScrutineeTermElaboration Raw
  | MatchScrutineeElaboration CScrutinee
  | CompareSyntaxCatGuess Raw Raw
  | JudgementFormElaboration Variable
  deriving (Show)

data Complaint
  -- scope
  = OutOfScope Range Variable
  | MetaScopeTooBig Range Variable ObjVars ObjVars
  | VariableShadowing Range Variable
  | EmptyContext Range
  | NotTopVariable Range Variable Variable
  | IncompatibleChannelScopes Range ObjVars ObjVars
  | NotAValidContextRestriction Th ObjVars
  | NotAValidDescriptionRestriction Th ASemanticsDesc
  -- kinding
  | NotAValidTermVariable Range Variable Kind
  | NotAValidPatternVariable Range Variable Resolved
  | NotAValidJudgement Range Variable Resolved
  | NotAValidStack Range Variable Resolved
  | NotAValidChannel Range Variable Resolved
  | NotAValidBoundVar Range Variable
  | NotAValidSubjectVar Range Variable
  | NotAValidOperator Range String
  -- operators
  | AlreadyDeclaredOperator Range String
  | InvalidOperatorArity Range String [SyntaxDesc] [RawP]
  | ExpectedParameterBinding Range Raw
  -- protocol
  | InvalidSend Range Channel Raw
  | InvalidRecv Range Channel RawP
  | NonLinearChannelUse Range Channel
  | UnfinishedProtocol Range Channel AProtocol
  | InconsistentCommunication Range
  | DoomedBranchCommunicated Range CActor
  | ProtocolsNotDual Range AProtocol AProtocol
  | IncompatibleModes Range AProtocolEntry AProtocolEntry
  | WrongDirection Range AProtocolEntry Ordering AProtocolEntry
  -- judgementforms
  | JudgementWrongArity Range JudgementName AProtocol [CFormula]
  | UnexpectedNonSubject Range CFormula
  | DuplicatedPlace Range Variable
  | DuplicatedInput Range Variable
  | DuplicatedOutput Range Variable
  | BothInputOutput Range Variable
  | ProtocolCitizenSubjectMismatch Range Variable (Mode ())
  | MalformedPostOperator Range String [Variable]
  -- syntaxes
  | AlreadyDeclaredSyntaxCat Range SyntaxCat
  -- syntaxdesc validation
  | InconsistentSyntaxDesc Range
  | InvalidSyntaxDesc Range SyntaxDesc
  | IncompatibleSyntaxInfos Range (Info SyntaxDesc) (Info SyntaxDesc)
  | IncompatibleSemanticsDescs Range ASemanticsDesc ASemanticsDesc
  | GotBarredAtom Range String [String]
  | ExpectedNilGot Range String
  | ExpectedEnumGot Range [String] String
  | ExpectedTagGot Range [String] String
  | ExpectedANilGot Range Raw
  | ExpectedANilPGot Range RawP
  | ExpectedAConsGot Range Raw
  | ExpectedAConsPGot Range RawP
  | SyntaxError Range ASemanticsDesc Raw
  | SyntaxPError Range ASemanticsDesc RawP
  | ExpectedAnOperator Range Raw
  | ExpectedAnEmptyListGot Range String [SyntaxDesc]
  -- semanticsdesc validation
  | InvalidSemanticsDesc Range ASemanticsDesc
  | SemanticsError Range ASemanticsDesc Raw
  | IncompatibleSemanticsInfos Range (Info ASemanticsDesc) (Info ASemanticsDesc)
  -- subjects and citizens
  | AsPatternCannotHaveSubjects Range RawP
  -- desc inference
  | InferredDescMismatch Range
  | DontKnowHowToInferDesc Range Raw
  | ArityMismatchInOperator Range
  | SchematicVariableNotInstantiated Range
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
    NotAValidSubjectVar r _ -> r
    NotAValidOperator r _ -> r
  -- operators
    AlreadyDeclaredOperator r _ -> r
    InvalidOperatorArity r _ _ _ -> r
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
    JudgementWrongArity r _ _ _ -> r
    UnexpectedNonSubject r _ -> r
    DuplicatedPlace r _ -> r
    DuplicatedInput r _ -> r
    DuplicatedOutput r _ -> r
    BothInputOutput r _ -> r
    ProtocolCitizenSubjectMismatch r _ _ -> r
    MalformedPostOperator r _ _ -> r
  -- syntaxes
    AlreadyDeclaredSyntaxCat r _ -> r
  -- syntaxdesc validation
    InconsistentSyntaxDesc r -> r
    InvalidSyntaxDesc r _ -> r
    IncompatibleSyntaxInfos r _ _ -> r
    IncompatibleSemanticsDescs r _ _ -> r
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
    -- semantics validation
    InvalidSemanticsDesc r _ -> r
    SemanticsError r _ _ -> r
    IncompatibleSemanticsInfos r  _ _ -> r
    -- subjects and citizens
    AsPatternCannotHaveSubjects r _ -> r
    -- desc inference
    InferredDescMismatch r -> r
    DontKnowHowToInferDesc r _ -> r
    ArityMismatchInOperator r -> r
    SchematicVariableNotInstantiated r -> r

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

data Resolved
  = ADeclaration Kind
  | AnObjVar ASemanticsDesc DB
  | AMacro Raw
  deriving Show

resolve :: Variable -> Elab (Maybe Resolved)
resolve (Variable r x) = do
  ctx <- ask
  let ds  = declarations ctx
  let ovs = getObjVars . objVars $ ctx
  let mcs = macros ctx
  pure $ case focusBy (\ (y, k) -> k <$ guard (x == y)) ds of
    Just (_, k, _) -> Just $ ADeclaration k
    _ -> case focusBy (\ (ObjVar y desc) -> desc <$ guard (x == y)) ovs of
      Just (xz, desc, xs) ->
        -- no need to weaken desc as it's already living in ctx
        Just $ AnObjVar desc (DB $ length xs)
      Nothing -> case focusBy (\ (y, k) -> k <$ guard (x == y)) mcs of
        Just (_, t, _) -> Just $ AMacro t
        Nothing -> Nothing

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
