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
import Syntax (SyntaxCat, SyntaxDesc, SyntaxTable)
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
import Data.Void (absurd)

------------------------------------------------------------------------------
-- Elaboration Monad

asSemantics :: ASyntaxDesc -> ASemanticsDesc
asSemantics syn = fmap absurd $^ syn

data ElabState = ElabState
  { channelStates :: ChannelStates
  , actvarStates  :: ActvarStates
  , syntaxCats    :: SyntaxTable
  , warnings      :: Bwd (WithStackTrace (WithRange Warning))
  , clock         :: Int
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
initElabState = ElabState Map.empty Map.empty Map.empty B0 0

newtype Elab a = Elab
  { runElab :: StateT ElabState
               (ReaderT Context
               (WriterT All       -- Can we win?
               (Either (WithStackTrace (WithRange Complaint)))))
               a }
  deriving ( Functor, Applicative, Monad
           , MonadReader Context
           , MonadState ElabState
           , MonadWriter All)

instance MonadError (WithRange Complaint) Elab where
  throwError err = do
    stk <- asks stackTrace
    Elab (throwError (WithStackTrace stk err))

  catchError ma k = Elab (catchError (runElab ma) (runElab . k . theMessage))

throwComplaint :: HasGetRange a => a -> Complaint -> Elab b
throwComplaint r c = throwError (WithRange (getRange r) c)

evalElab :: Options -> Elab a -> Either (WithStackTrace (WithRange Complaint)) a
evalElab opts = fmap fst
         . runWriterT
         . (`runReaderT` initContext opts)
         . (`evalStateT` initElabState)
         . runElab

------------------------------------------------------------------------------
-- Partial Info

infoExpand :: HeadUpData' ActorMeta -> SyntaxTable -> ASemanticsDesc -> Info VSemanticsDesc
infoExpand dat table s = case Semantics.expand table dat s of
  Nothing -> Inconsistent
  Just (VWildcard _) -> Unknown
  Just a -> Known a

satom :: String -> Elab ACTm
satom at = atom at <$> asks (scopeSize . objVars)

fromInfo :: Range -> Info ASemanticsDesc -> Elab ASemanticsDesc
fromInfo r Unknown = satom "Wildcard"
fromInfo r (Known desc) = pure desc
-- I believe this last case is currently unreachable because this
-- may only arise from a call to (<>) and this is only used in two
-- places:
-- 1. `addHint` (and if we had a clash, that'd be a shadowing error)
-- 2. `compatibleInfos` where the error is handled locally
fromInfo r Inconsistent = throwComplaint r InconsistentSyntaxDesc

incompatibleSemanticsDescs :: ASemanticsDesc -> ASemanticsDesc -> Elab Complaint
incompatibleSemanticsDescs desc desc' = do
  vars <- withVarNames ()
  pure $ IncompatibleSemanticsDescs (desc <$ vars) (desc' <$ vars)

incompatibleSemanticsInfos :: Info ASemanticsDesc -> Info ASemanticsDesc -> Elab Complaint
incompatibleSemanticsInfos desc desc' = do
  vars <- withVarNames ()
  pure $ IncompatibleSemanticsInfos (fmap (<$ vars) desc) (fmap (<$ vars) desc')

syntaxError :: ASemanticsDesc -> Raw -> Elab Complaint
syntaxError desc t = do
  desc <- withVarNames desc
  pure (SyntaxError desc t)

syntaxPError :: ASemanticsDesc -> RawP -> Elab Complaint
syntaxPError desc p = do
  desc <- withVarNames desc
  pure (SyntaxPError desc p)

compatibleInfos :: Range
                -> Info ASemanticsDesc
                -> Info ASemanticsDesc
                -> Elab (Info ASemanticsDesc)
compatibleInfos r desc desc' = do
  table <- gets syntaxCats
  dat <- asks headUpData
  let de = infoExpand dat table =<< desc
  let de' = infoExpand dat table =<< desc'
  case de <> de' of
    Inconsistent -> throwComplaint r =<< case (desc, desc') of
      (Known desc, Known desc') -> incompatibleSemanticsDescs desc desc'
      _ -> incompatibleSemanticsInfos desc desc'
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

instance Dischargeable Decls where
  x \\ ds = ds

-- LexicalScope = ObjVars + Macros
-- gives the meanings of things that look like variables.

-- Crucially, only the ObjVars are in scope for the abstract syntax
-- and their semantics desc is in the scope of the whole context,
-- i.e. ObjVars are ready for lookup with no further weakening.
-- Consequently, we must weaken them when we go under a binder.

type Macros = Bwd (String, Raw)
-- Macros are scope checked at definition site but not elaborated
-- until use site. They cannot be recursive.
-- The vars that occur in a Macro are CdBVars - we have checked they are
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

data Restriction {- gamma -} = Restriction
  { support :: Bwd String
  , restriction :: Th {- support -} {- gamma -}
  }

initRestriction :: ObjVars -> Restriction
initRestriction ovs = Restriction (objVarName <$> getObjVars ovs) (ones (scopeSize ovs))

extend :: Restriction {- gamma -}
       -> {- x :: -} Binder String
       -> Restriction {- gamma , x -}
extend (Restriction ls th) (Used x) = Restriction (ls :< x) (th -? True)
extend (Restriction ls th) Unused = Restriction ls (th -? False)

instance Selable Restriction where
  ph ^? Restriction ls th = Restriction (ph ^? ls) (ph ^? th)

data ElabMode = Definition | Execution deriving (Eq, Show)

data WithVarNames a = WithVarNames
  { varNames :: Bwd String
  , scopedValue :: a
  } deriving (Show, Functor)

withVarNames :: t -> Elab (WithVarNames t)
withVarNames t = do
  ovs <- asks (fmap objVarName . getObjVars . objVars)
  pure (WithVarNames ovs t)

initContext :: Options -> Context
initContext opts = Context
  { objVars = ObjVars B0
  , macros = B0
  , declarations = B0
  , operators = Map.fromList
    [ ("app", AnOperator
        { opName = Operator "app"
        , objDesc = (Unused, PP (AP "Pi")
                              $ PP (MP (am "S") (ones 0))
                                $ PP (BP (Hide "x")
                                  $ MP (am "T") (ones 1)) $ AP "")
        , paramsDesc = [(Used (am "s"), ObjVars B0 :=> (am "S" $: sbstI 0))]
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
declareObjVar :: ( {- x :: -} String
                 , {- S :: -} ASemanticsDesc {- gamma -})
              -> Context {- gamma -}
              -> Context {- gamma, x :: S -}
declareObjVar (x, sem) ctx =
    -- We store semantics descs ready to be deployed at use sites
    let scp = getObjVars (objVars ctx) :< ObjVar x sem in
    ctx { objVars = ObjVars (fmap weak <$> scp)
        , binderHints = fmap weak <$> binderHints ctx
        }

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

setMacros :: Macros -> Context -> Context
setMacros ms ctx = ctx { macros = ms }

declareMacro :: (String, Raw) -> Context -> Context
declareMacro xt ctx = ctx { macros = macros ctx :< xt }

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

-- TODO: hints should be ASOTs
addHint :: Binder String -> Info ASemanticsDesc -> Context -> Context
addHint Unused cat ctx = ctx
addHint (Used str) cat ctx =
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
  = UnreachableClause RawP
  | MissingClauses (NonEmpty RawP)
  -- Subject tracking
  | SentSubjectNotASubjectVar Raw
  | RecvSubjectNotScrutinised Channel (Binder String)
  | PatternSubjectNotScrutinised String
  | UnderscoreOnSubject
  | InconsistentScrutinisation
  -- Missing features
  | IgnoredIrrefutable RawP

raiseWarning :: HasGetRange a => a -> Warning -> Elab ()
raiseWarning a w = do
  stk <- asks stackTrace
  let warning = WithStackTrace stk (WithRange (getRange a) w)
  modify (\ st -> st { warnings = warnings st :< warning })

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
  | SubstitutionElaboration (Bwd Assign)
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

type ESemanticsDesc = WithVarNames ASemanticsDesc

data Complaint
  -- scope
  = OutOfScope Variable
  | MetaScopeTooBig Variable ObjVars ObjVars
  | VariableShadowing Variable
  | EmptyContext
  | NotTopVariable Variable Variable
  | IncompatibleChannelScopes ObjVars ObjVars
  | NotAValidContextRestriction Th ObjVars
  | NotAValidDescriptionRestriction Th ESemanticsDesc
  -- kinding
  | NotAValidTermVariable Variable Kind
  | NotAValidPatternVariable Variable Resolved
  | NotAValidJudgement Variable Resolved
  | NotAValidStack Variable Resolved
  | NotAValidChannel Variable Resolved
  | NotAValidBoundVar Variable
  | NotAValidSubjectVar Variable
  | NotAValidOperator String
  -- operators
  | AlreadyDeclaredOperator String
  | ArityMismatchInOperator String Int
  | ExpectedParameterBinding Raw
  -- protocol
  | InvalidSend Channel Raw
  | InvalidRecv Channel RawP
  | NonLinearChannelUse Channel
  | UnfinishedProtocol Channel AProtocol
  | InconsistentCommunication
  | DoomedBranchCommunicated CActor
  | ProtocolsNotDual AProtocol AProtocol
  | IncompatibleModes AProtocolEntry AProtocolEntry
  | WrongDirection AProtocolEntry Ordering AProtocolEntry
  -- judgementforms
  | JudgementWrongArity JudgementName AProtocol [CFormula]
  | UnexpectedNonSubject CFormula
  | DuplicatedPlace Variable
  | DuplicatedInput Variable
  | DuplicatedOutput Variable
  | BothInputOutput Variable
  | ProtocolCitizenSubjectMismatch Variable (Mode ())
  | MalformedPostOperator String [Variable]
  -- syntaxes
  | AlreadyDeclaredSyntaxCat SyntaxCat
  -- syntaxdesc validation
  | InconsistentSyntaxDesc
  | InvalidSyntaxDesc SyntaxDesc
  | IncompatibleSyntaxInfos (Info SyntaxDesc) (Info SyntaxDesc)
  | IncompatibleSemanticsDescs ESemanticsDesc ESemanticsDesc
  | GotBarredAtom String [String]
  | ExpectedASemanticsGot Raw
  | ExpectedNilGot String
  | ExpectedEnumGot [String] String
  | ExpectedTagGot [String] String
  | ExpectedANilGot Raw
  | ExpectedANilPGot RawP
  | ExpectedAConsGot Raw
  | ExpectedAConsPGot RawP
  | ExpectedASemanticsPGot RawP
  | SyntaxError ESemanticsDesc Raw
  | SyntaxPError ESemanticsDesc RawP
  | CantMatchOnPi ESemanticsDesc RawP
  | DuplicatedTag String
  | ExpectedAnOperator Raw
  | ExpectedAnEmptyListGot String [SyntaxDesc]
  -- semanticsdesc validation
  | InvalidSemanticsDesc ESemanticsDesc
  | SemanticsError ESemanticsDesc Raw
  | IncompatibleSemanticsInfos (Info ESemanticsDesc) (Info ESemanticsDesc)
  -- subjects and citizens
  | AsPatternCannotHaveSubjects RawP
  -- desc inference
  | InferredDescMismatch (WithVarNames Pat) ESemanticsDesc
  | DontKnowHowToInferDesc Raw
  | SchematicVariableNotInstantiated
  deriving (Show)

------------------------------------------------------------------------------
-- Syntaxes

declareSyntax :: WithRange SyntaxCat -> SyntaxDesc -> Elab ()
declareSyntax (WithRange r cat) desc = do
  st <- get
  whenJust (Map.lookup cat (syntaxCats st)) $ \ _ ->
    throwComplaint r (AlreadyDeclaredSyntaxCat cat)
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
