module Elaboration where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Function
import Data.List (isPrefixOf)
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

import Actor
import Bwd
import Concrete.Base
import Format
import Hide
import Scope
import Syntax
import Thin
import Utils

import Term.Base
import Term.Substitution
import Pattern as P
import Location

dual :: Protocol t -> Protocol t
dual = map $ \case
  (Input, c) -> (Output, c)
  (Output, c) -> (Input, c)

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

compatibleInfos :: Info SyntaxDesc -> Info SyntaxDesc -> Elab (Info SyntaxDesc)
compatibleInfos desc desc' = do
  table <- gets syntaxCats
  let de = infoExpand table =<< desc
  let de' = infoExpand table =<< desc'
  case de <> de' of
    Inconsistent -> throwError (IncompatibleSyntaxInfos desc desc')
    d -> pure $ case (desc, desc') of
      (Known (CdB (A _) _), _) -> desc
      (_, Known (CdB (A _) _)) -> desc'
      _ -> Syntax.contract <$> d

type ObjVar = (String, Info SyntaxDesc)
type ObjVars = Bwd ObjVar

data Kind
  = ActVar (Info SyntaxDesc) ObjVars
  | AChannel ObjVars
  | AJudgement ExtractMode (Maybe AJudgementStack) AProtocol
  deriving (Show)

type Hints = Map String (Info SyntaxDesc)

data Context = Context
  { objVars      :: ObjVars
  , declarations :: Decls
  , location     :: Bwd Turn
  , binderHints  :: Hints
  , currentActor :: (JudgementForm, Maybe AJudgementStack)
  } deriving (Show)

setCurrentActor :: JudgementForm -> Maybe AJudgementStack -> Context -> Context
setCurrentActor jd mstk ctx = ctx { currentActor = (jd, mstk) }

initContext :: Context
initContext = Context B0 B0 B0 Map.empty ("", Nothing)

data Turn = West | East
  deriving (Show, Eq)

declareObjVar :: ObjVar -> Context -> Context
declareObjVar x ctx = ctx { objVars = objVars ctx :< x }

setObjVars :: ObjVars -> Context -> Context
setObjVars ovs ctx = ctx { objVars = ovs }

instance Selable Context where
  th ^? ctxt = ctxt { objVars = th ^? objVars ctxt }

declare :: Binder String -> Kind -> Context -> Context
declare Unused k ctx = ctx
declare (Used x) k ctx = ctx { declarations = declarations ctx :< (x, k) }

turn :: Turn -> Context -> Context
turn t ds = ds { location = location ds :< t }

setDecls :: Decls -> Context -> Context
setDecls ds ctx = ctx { declarations = ds }

setHints :: Hints -> Context -> Context
setHints hs ctx = ctx { binderHints = hs }

type Decls = Bwd (String, Kind)
type Slced = [(String, Kind)]
type Focus a = (Decls, a, Slced)

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

isFresh :: Variable -> Elab String
isFresh x = do
  res <- resolve x
  whenJust res $ \ _ -> throwError (VariableShadowing (getRange x) x)
  pure (getVariable x)

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
  | NotAValidChannel Range Variable (Maybe Kind)
  | NotAValidBoundVar Range Variable
  -- protocol
  | InvalidSend Range Channel Raw
  | InvalidRecv Range Channel (Binder String)
  | NonLinearChannelUse Channel
  | UnfinishedProtocol Channel AProtocol
  | InconsistentCommunication
  | DoomedBranchCommunicated CActor
  | ProtocolsNotDual Range AProtocol AProtocol
  | IncompatibleModes Range (Mode, SyntaxDesc) (Mode, SyntaxDesc)
  | WrongDirection Range (Mode, SyntaxDesc) Ordering (Mode, SyntaxDesc)
  -- judgement stacks
  | PushingOnAStacklessJudgement Range JudgementForm
  | LookupFromAStacklessActor Range JudgementForm
  -- syntaxes
  | NotAValidSyntaxCat SyntaxCat
  | AlreadyDeclaredSyntaxCat SyntaxCat
  | SyntaxContainsMeta SyntaxCat
  | InvalidSyntax SyntaxCat
  -- syntaxdesc validation
  | InconsistentSyntaxDesc
  | InvalidSyntaxDesc SyntaxDesc
  | IncompatibleSyntaxInfos (Info SyntaxDesc) (Info SyntaxDesc)
  | IncompatibleSyntaxDescs Range SyntaxDesc SyntaxDesc
  | ExpectedNilGot Range String
  | ExpectedEnumGot Range [String] String
  | ExpectedTagGot Range [String] String
  | ExpectedANilGot Range Raw
  | ExpectedANilPGot Range RawP
  | ExpectedAConsGot Range Raw
  | ExpectedAConsPGot Range RawP
  | SyntaxError Range SyntaxDesc Raw
  | SyntaxPError Range SyntaxDesc RawP
  -- contextual info
  -- shouldn't contain ranges because there should be a more precise one
  -- on the decorated complaint
  | SendTermElaboration Channel Raw Complaint
  | MatchTermElaboration Raw Complaint
  | MatchElaboration Raw Complaint
  | MatchBranchElaboration RawP Complaint
  | ConstrainTermElaboration Raw Complaint
  | ConstrainSyntaxCatGuess Raw Raw Complaint
  | FreshMetaElaboration Complaint
  | UnderElaboration Complaint
  | RecvMetaElaboration Channel Complaint
  | PushTermElaboration Raw Complaint
  | LookupTermElaboration Raw Complaint
  | LookupHandlersElaboration Raw Complaint
  | DeclJElaboration Variable Complaint
  | DefnJElaboration Variable Complaint
  | ExecElaboration Complaint
  | DeclaringSyntaxCat SyntaxCat Complaint
  | SubstitutionElaboration (Bwd SbstC) Complaint
  | PatternVariableElaboration Variable Complaint
  | TermVariableElaboration Variable Complaint
  | ProtocolElaboration CProtocol Complaint
  | ConnectElaboration Variable Variable Complaint
  deriving (Show)

instance HasRange Complaint where
  setRange _ = id -- FIXME

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
    NotAValidChannel r _ _ -> r
    NotAValidBoundVar r _ -> r
  -- protocol
    InvalidSend r _ _ -> r
    InvalidRecv r _ _ -> r
    NonLinearChannelUse _ -> unknown
    UnfinishedProtocol _ _ -> unknown
    InconsistentCommunication -> unknown
    DoomedBranchCommunicated _ -> unknown
    ProtocolsNotDual r _ _ -> r
    IncompatibleModes r _ _ -> r
    WrongDirection r _ _ _ -> r
  -- judgement stacks
    PushingOnAStacklessJudgement r _ -> r
    LookupFromAStacklessActor r _ -> r
  -- syntaxes
    NotAValidSyntaxCat _ -> unknown
    AlreadyDeclaredSyntaxCat _ -> unknown
    SyntaxContainsMeta _ -> unknown
    InvalidSyntax _ -> unknown
  -- syntaxdesc validation
    InconsistentSyntaxDesc -> unknown
    InvalidSyntaxDesc _ -> unknown
    IncompatibleSyntaxInfos _ _ -> unknown
    IncompatibleSyntaxDescs r _ _ -> r
    ExpectedNilGot r _ -> r
    ExpectedEnumGot r _ _ -> r
    ExpectedTagGot r _ _ -> r
    ExpectedANilGot r _ -> r
    ExpectedANilPGot r _ -> r
    ExpectedAConsGot r _ -> r
    ExpectedAConsPGot r _ -> r
    SyntaxError r _ _ -> r
    SyntaxPError r _ _ -> r
  -- contextual info
  -- shouldn't contain ranges because there should be a more precise one
  -- on the decorated complaint
    SendTermElaboration _ _ c -> getRange c
    MatchTermElaboration _ c -> getRange c
    MatchElaboration _ c -> getRange c
    MatchBranchElaboration _ c -> getRange c
    ConstrainTermElaboration _ c -> getRange c
    ConstrainSyntaxCatGuess _ _ c -> getRange c
    FreshMetaElaboration c -> getRange c
    UnderElaboration c -> getRange c
    RecvMetaElaboration _ c -> getRange c
    PushTermElaboration _ c -> getRange c
    LookupTermElaboration _ c -> getRange c
    LookupHandlersElaboration _ c -> getRange c
    DeclJElaboration _ c -> getRange c
    DefnJElaboration _ c -> getRange c
    ExecElaboration c -> getRange c
    DeclaringSyntaxCat _ c -> getRange c
    SubstitutionElaboration _ c -> getRange c
    PatternVariableElaboration _ c -> getRange c
    TermVariableElaboration _ c -> getRange c
    ProtocolElaboration _ c -> getRange c
    ConnectElaboration _ _ c -> getRange c

data ElabState = ElabState
  { channelStates :: Map Channel ([Turn], AProtocol)
  , syntaxCats    :: SyntaxTable
  } deriving (Eq)

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

fromInfo :: Info SyntaxDesc -> Elab SyntaxDesc
fromInfo Unknown = pure (atom "Wildcard" 0)
fromInfo (Known desc) = pure desc
fromInfo Inconsistent = throwError InconsistentSyntaxDesc

declareSyntax :: SyntaxCat -> SyntaxDesc -> Elab ()
declareSyntax cat desc = do
  st <- get
  whenJust (Map.lookup cat (syntaxCats st)) $ \ _ ->
    throwError (AlreadyDeclaredSyntaxCat cat)
  put (st { syntaxCats = Map.insert cat desc (syntaxCats st) })

channelLookup :: Channel -> ElabState -> Maybe ([Turn], AProtocol)
channelLookup ch = Map.lookup ch . channelStates

channelInsert :: Channel -> ([Turn], AProtocol) -> ElabState -> ElabState
channelInsert ch x st = st { channelStates = Map.insert ch x (channelStates st) }

channelDelete :: Channel -> ElabState -> ElabState
channelDelete ch st = st { channelStates = Map.delete ch (channelStates st) }

initElabState :: ElabState
initElabState = ElabState Map.empty Map.empty

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

withSyntax :: SyntaxDesc -> Elab a -> Elab a
withSyntax desc ma = do
  st <- get
  put $ st { syntaxCats = Map.singleton "Syntax" desc }
  a <- ma
  put $ st { syntaxCats = syntaxCats st }
  pure a

during :: (Complaint -> Complaint) -> Elab a -> Elab a
during f ma = ma `catchError` (throwError . f)

evalElab :: Elab a -> Either Complaint a
evalElab = fmap fst
         . runWriterT
         . (`runReaderT` initContext)
         . (`evalStateT` initElabState)
         . runElab

type ACTm = CdB (Tm ActorMeta)
type ACTSbst = CdB (Sbst ActorMeta)

svar :: Variable -> Elab (Info SyntaxDesc, ACTm)
svar x = do
  ovs <- asks objVars
  res <- resolve x
  case res of
    Just (Left k) -> case k of -- TODO: come back and remove fst <$>
      ActVar desc sc -> case findSub (fst <$> sc) (fst <$> ovs) of
        Just th -> pure (desc, ActorMeta (getVariable x) $: sbstW (sbst0 0) th)
        Nothing -> throwError (MetaScopeTooBig (getRange x) x sc ovs)
      _ -> throwError (NotAValidTermVariable (getRange x) x k)
    Just (Right (desc, i)) -> pure (desc, var i (length ovs))
    Nothing -> throwError (OutOfScope (getRange x) x)

getName :: Elab [Turn]
getName = do
  loc <- asks location
  pure (loc <>> [])

spop :: Range -> Elab (ObjVars, (Variable, Info SyntaxDesc))
spop r = do
  ovs <- asks objVars
  case ovs of
    B0 -> throwError (EmptyContext r)
    (xz :< (x, cat)) -> pure (xz, (Variable r x, cat))

ssyntaxdecl :: [SyntaxCat] -> Raw -> Elab SyntaxDesc
ssyntaxdecl syndecls syn = do
  let desc = catToDesc "Syntax"
  syn <- withSyntax (syntaxDesc syndecls) $ stm desc syn
  case isMetaFree syn of
    Nothing -> throwError undefined -- this should be impossible, since parsed in empty context
    Just syn0 -> pure syn0

ssbst :: Bwd SbstC -> Elab (ACTSbst, ObjVars)
ssbst B0 = do
    ovs <- asks objVars
    pure (sbstI (length ovs), ovs)
ssbst (sg :< sgc) = case sgc of
    Keep r v -> do
      (xz, (w, cat)) <- spop r
      when (v /= w) $ throwError (NotTopVariable r v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst sg)
      pure (sbstW sg (ones 1), ovs :< (getVariable w, cat))
    Drop r v -> do
      (xz, (w, cat)) <- spop r
      when (v /= w) $ throwError (NotTopVariable r v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst sg)
      pure (weak sg, ovs)
    Assign r v t -> do
      info <- getHint (getVariable v)
      desc <- fromInfo info
      t <- stm desc t
      (sg, ovs) <- ssbst sg
      v <- local (setObjVars ovs) $ isFresh v
      pure (sbstT sg ((Hide v :=) $^ t), ovs :< (v, info))

sth :: (Bwd Variable, ThDirective) -> Elab Th
sth (xz, b) = do
  ovs <- asks objVars
  let th = which (`elem` (getVariable <$> xz)) (fst <$> ovs)
  pure $ case b of
    ThKeep -> th
    ThDrop -> comp th

stms :: [SyntaxDesc] -> Raw -> Elab ACTm
stms [] (At r "") = atom "" <$> asks (length . objVars)
stms [] (At r a) = throwError (ExpectedNilGot r a)
stms [] t = throwError (ExpectedANilGot (getRange t) t)
stms (d:ds) (Cons r p q) = (%) <$> stm d p <*> stms ds q
stms _ t = throwError (ExpectedAConsGot (getRange t) t)

stm :: SyntaxDesc -> Raw -> Elab ACTm
stm desc (Var r v) = during (TermVariableElaboration v) $ do
  table <- gets syntaxCats
  (desc', t) <- svar v
  compatibleInfos (Known desc) desc'
  pure t
stm desc (Sbst r sg t) = do
    (sg, ovs) <- during (SubstitutionElaboration sg) $ ssbst sg
    t <- local (setObjVars ovs) (stm desc t)
    pure (t //^ sg)
stm desc rt = do
  table <- gets syntaxCats
  case Syntax.expand table desc of
    Nothing -> throwError (InvalidSyntaxDesc desc)
    Just vdesc -> case rt of
      At r a -> do
        case vdesc of
          VAtom -> pure ()
          VNil -> unless (a == "") $ throwError (ExpectedNilGot r a)
          VNilOrCons{} -> unless (a == "") $ throwError (ExpectedNilGot r a)
          VEnumOrTag es _ -> unless (a `elem` es) $ throwError (ExpectedEnumGot r es a)
          VWildcard -> pure ()
          _ -> throwError (SyntaxError r desc rt)
        atom a <$> asks (length . objVars)
      Cons r p q -> case vdesc of
        VNilOrCons d1 d2 -> (%) <$> stm d1 p <*> stm d2 q
        VCons d1 d2 -> (%) <$> stm d1 p <*> stm d2 q
        VWildcard -> (%) <$> stm desc p <*> stm desc q
        VEnumOrTag _ ds -> case p of
          At r a -> case lookup a ds of
            Nothing -> throwError (ExpectedTagGot r (fst <$> ds) a)
            Just descs -> (%) <$> stm (atom "Atom" 0) p <*> stms descs q
          _ -> throwError (SyntaxError r desc rt)
        _ -> throwError (SyntaxError r desc rt)
      Lam r (Scope (Hide x) sc) -> do
        (s, desc) <- case vdesc of
          VWildcard -> pure (Unknown, desc)
          VBind cat desc -> pure (Known (catToDesc cat), desc)
          _ -> throwError (SyntaxError r desc rt)
        case x of
          Used x -> do
            x <- isFresh x
            sc <- local (declareObjVar (x, s)) $ stm desc sc
            pure (x \\ sc)
          Unused -> do
            sc <- stm desc sc
            pure ((Hide "_" := False :.) $^ sc)

spats :: [SyntaxDesc] -> RawP -> Elab (Pat, Decls, Hints)
spats [] (AtP r "") = (AP "",,) <$> asks declarations <*> asks binderHints
spats [] (AtP r a) = throwError (ExpectedNilGot r a)
spats [] t = throwError (ExpectedANilPGot (getRange t) t)
spats (d:ds) (ConsP r p q) = do
  (p, decls, hints) <- spat d p
  (q, decls, hints) <- local (setDecls decls . setHints hints) $ spats ds q
  pure (PP p q, decls, hints)
spats _ t = throwError (ExpectedAConsPGot (getRange t) t)

spat :: SyntaxDesc -> RawP -> Elab (Pat, Decls, Hints)
spat desc (VarP r v) = during (PatternVariableElaboration v) $ do
  table <- gets syntaxCats
  ds <- asks declarations
  hs <- asks binderHints
  res <- resolve v
  case res of
    Just (Left k)  -> throwError (NotAValidPatternVariable r v k)
    Just (Right (desc', i)) -> do
      compatibleInfos (Known desc) desc'
      pure (VP i, ds, hs)
    Nothing -> do
      ovs <- asks objVars
      v <- pure (getVariable v)
      pure (MP v (ones (length ovs)), ds :< (v, ActVar (Known desc) ovs), hs)
spat desc (ThP r th p) = do
  th <- sth th
  (p, ds, hs) <- local (th ^?) $ spat desc p
  pure (p *^ th, ds, hs)
spat desc (UnderscoreP r) = (HP,,) <$> asks declarations <*> asks binderHints
spat desc rp = do
  table <- gets syntaxCats
  case Syntax.expand table desc of
    Nothing -> throwError (InvalidSyntaxDesc desc)
    Just vdesc -> case rp of
      AtP r a -> do
        case vdesc of
          VAtom -> pure ()
          VNil -> unless (a == "") $ throwError (ExpectedNilGot r a)
          VNilOrCons{} -> unless (a == "") $ throwError (ExpectedNilGot r a)
          VEnumOrTag es _ -> unless (a `elem` es) $ throwError (ExpectedEnumGot r es a)
          VWildcard -> pure ()
          _ -> throwError (SyntaxPError r desc rp)
        (AP a,,) <$> asks declarations <*> asks binderHints

      ConsP r p q -> case vdesc of
        VNilOrCons d1 d2 -> do
          (p, ds, hs) <- spat d1 p
          (q, ds, hs) <- local (setDecls ds . setHints hs) (spat d2 q)
          pure (PP p q, ds, hs)
        VCons d1 d2 -> do
          (p, ds, hs) <- spat d1 p
          (q, ds, hs) <- local (setDecls ds . setHints hs) (spat d2 q)
          pure (PP p q, ds, hs)
        VWildcard -> do
          (p, ds, hs) <- spat desc p
          (q, ds, hs) <- local (setDecls ds . setHints hs) (spat desc q)
          pure (PP p q, ds, hs)
        VEnumOrTag _ ds -> case p of
          AtP r a -> case lookup a ds of
            Nothing -> throwError (ExpectedTagGot r (fst <$> ds) a)
            Just descs ->  do
              (p, ds, hs) <- spat (atom "Atom" 0) p
              (q, ds, hs) <- local (setDecls ds . setHints hs) (spats descs q)
              pure (PP p q, ds, hs)
          _ -> throwError (SyntaxPError r desc rp)
        _ -> throwError (SyntaxPError r desc rp)

      LamP r (Scope v@(Hide x) p) -> do
        (s, desc) <- case vdesc of
          VWildcard -> pure (Unknown, desc)
          VBind cat desc -> pure (Known (catToDesc cat), desc)
          _ -> throwError (SyntaxPError r desc rp)

        case x of
          Unused -> do
            (p, ds, hs) <- spat desc p
            pure (BP (Hide "_") p, ds, hs)
          Used x -> do
            x <- isFresh x
            (p, ds, hs) <- local (declareObjVar (x, s) . addHint x s) $ spat desc p
            pure (BP (Hide x) p, ds, hs)

isChannel :: Variable -> Elab Channel
isChannel ch = resolve ch >>= \case
  Just (Left (AChannel sc)) -> pure (Channel $ getVariable ch)
  Just mk -> throwError (NotAValidChannel (getRange ch) ch $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope (getRange ch) ch)

data IsJudgement = IsJudgement
  { judgementExtract :: ExtractMode
  , judgementName :: JudgementForm
  , judgementStack :: Maybe AJudgementStack
  , judgementProtocol :: AProtocol
  }

isJudgement :: Variable -> Elab IsJudgement
isJudgement jd = resolve jd >>= \case
  Just (Left (AJudgement em mstk p)) -> pure (IsJudgement em (getVariable jd) mstk p)
  Just mk -> throwError (NotAValidJudgement (getRange jd) jd $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope (getRange jd) jd)

channelScope :: Channel -> Elab ObjVars
channelScope (Channel ch) = do
  ds <- asks declarations
  case fromJust (focusBy (\ (y, k) -> k <$ guard (ch == y)) ds) of
    (_, AChannel sc, _) -> pure sc

steppingChannel :: Channel -> (AProtocol -> Elab (a, AProtocol)) ->
                   Elab a
steppingChannel ch step = do
  nm <- getName
  (pnm, p) <- gets (fromJust . channelLookup ch)
  unless (pnm `isPrefixOf` nm) $ throwError (NonLinearChannelUse ch)
  (cat, p) <- step p
  modify (channelInsert ch (nm, p))
  pure cat

open :: Channel -> AProtocol -> Elab ()
open ch p = do
  nm <- getName
  modify (channelInsert ch (nm, p))

close :: Channel -> Elab ()
close ch = do
  -- make sure the protocol was run all the way
  mp <- gets (channelLookup ch)
  case snd (fromJust mp) of
    [] -> pure ()
    p -> throwError (UnfinishedProtocol ch p)
  modify (channelDelete ch)

withChannel :: Channel -> AProtocol -> Elab a -> Elab a
withChannel ch@(Channel rch) p ma = do
  open ch p
  -- run the actor in the extended context
  ovs <- asks objVars
  a <- local (declare (Used rch) (AChannel ovs)) $ ma
  close ch
  pure a

guessDesc :: Bool -> -- is this in tail position?
             Raw -> Elab (Info SyntaxDesc)
guessDesc b (Var _ v) = resolve v >>= \case
  Just (Right (info, i)) -> pure info
  Just (Left (ActVar info _)) -> pure info
  _ -> pure Unknown
guessDesc b (Cons _ p q) = do
  dp <- guessDesc False p
  dq <- guessDesc True q
  case (dp, dq) of
    (Known d1, Known d2) -> pure (Known $ Syntax.contract (VCons d1 d2))
    _ -> pure Unknown
guessDesc True (At _ "") = pure (Known $ Syntax.contract VNil)
guessDesc _ _ = pure Unknown

compatibleChannels :: Range -> AProtocol -> Ordering -> AProtocol -> Elab Int
compatibleChannels r [] dir [] = pure 0
compatibleChannels r (p@(m, s) : ps) dir (q@(n, t) : qs) = do
  unless (s == t) $ throwError (IncompatibleSyntaxDescs r s t)
  when (m == n) $ throwError (IncompatibleModes r p q)
  case (m, dir) of
    (Input, LT) -> throwError (WrongDirection r p dir q)
    (Output, GT) -> throwError (WrongDirection r p dir q)
    _ -> pure ()
  (+1) <$> compatibleChannels r ps dir qs
compatibleChannels r ps _ qs = throwError (ProtocolsNotDual r ps qs)

sact :: CActor -> Elab AActor
sact = \case
  Win r -> pure (Win r)
  Constrain r s t -> do
    infoS <- guessDesc False s
    infoT <- guessDesc False t
    desc <- during (ConstrainSyntaxCatGuess s t) $
      fromInfo =<< compatibleInfos infoS infoT
    s <- during (ConstrainTermElaboration s) $ stm desc s
    t <- during (ConstrainTermElaboration t) $ stm desc t
    pure $ Constrain r s t

  Branch r a b -> do
    a <- local (turn West) $ sact a
    b <- local (turn East) $ sact b
    pure (Branch r a b)

  Spawn r em jd ch a -> do
    -- check the channel name is fresh & initialise it
    ch <- Channel <$> isFresh ch
    jd <- isJudgement jd

    a <- withChannel ch (dual $ judgementProtocol jd) $ sact a

    em <- pure $ case em of
      AlwaysExtract -> judgementExtract jd
      _ -> em

    pure $ Spawn r em (judgementName jd) ch a

  Send r ch tm a -> do
    ch <- isChannel ch
    -- Check the channel is in sending mode, & step it
    desc <- steppingChannel ch $ \case
      (Output, desc) : p -> pure (desc, p)
      _ -> throwError (InvalidSend r ch tm)

    -- Send
    tm <- during (SendTermElaboration ch tm) $ do
      sc <- channelScope ch
      ovs <- asks objVars
      let (thx, xyz, thy) = lintersection sc ovs
      (*^ thx) <$> local (setObjVars xyz) (stm desc tm)

    a <- sact a
    pure $ Send r ch tm a

  Recv r ch (av, a) -> do
    ch <- isChannel ch
    av <- during (RecvMetaElaboration ch) $ traverse isFresh av
    -- Check the channel is in receiving mode & step it
    cat <- steppingChannel ch $ \case
      (Input, cat) : p -> pure (cat, p)
      _ -> throwError (InvalidRecv r ch av)

    -- Receive
    sc <- channelScope ch
    a <- local (declare av (ActVar (Known cat) sc)) $ sact a
    pure $ Recv r ch (ActorMeta <$> av, a)

  Connect r (CConnect ch1 ch2) -> during (ConnectElaboration ch1 ch2) $ do
    ch1 <- isChannel ch1
    ch2 <- isChannel ch2
    p <- steppingChannel ch1 $ \ p -> pure (p, [])
    q <- steppingChannel ch2 $ \ p -> pure (p, [])
    sc1 <- channelScope ch1
    sc2 <- channelScope ch2
    (dir, th) <- case (findSub sc1 sc2, findSub sc2 sc1) of
      (Just thl, Just thr) -> pure (EQ, thl)
      (Just thl, _) -> pure (LT, thl)
      (_, Just thr) -> pure (GT, thr)
      _ -> throwError (IncompatibleChannelScopes r sc1 sc2)
    steps <- compatibleChannels r p dir q
    pure (aconnect r ch1 th ch2 steps)

  FreshMeta r desc (av, a) -> do
    (desc, av, ovs) <- during FreshMetaElaboration $ do
      syndecls <- gets (Map.keys . syntaxCats)
      desc <- ssyntaxdecl syndecls desc
      av <- isFresh av
      ovs <- asks objVars
      pure (desc, av, ovs)
    a <- local (declare (Used av) (ActVar (Known desc) ovs)) $ sact a
    pure $ FreshMeta r desc (ActorMeta av, a)

  Under r (Scope v@(Hide x) a) -> do
    during UnderElaboration $ () <$ isFresh x
    a <- local (declareObjVar (getVariable x, Unknown)) $ sact a
    pure $ Under r (Scope v a)

  Match r rtm@tm cls -> do
    desc <- fromInfo =<< guessDesc False rtm
    tm <- during (MatchTermElaboration tm) $ stm desc tm
    chs <- get
    clsts <- traverse (sclause desc) cls
    let (cls, sts) = unzip clsts
    during (MatchElaboration rtm) $ consistentCommunication sts
    pure $ Match r tm cls

  Push r jd (p, (), t) a -> do
    jd <- isJudgement jd
    stk <- case judgementStack jd of
      Nothing -> throwError (PushingOnAStacklessJudgement r (judgementName jd))
      Just stk -> pure stk

    p <- resolve p >>= \case
      Just (Right (cat, i)) -> i <$ compatibleInfos cat (Known $ keyDesc stk)
      Just (Left k) -> throwError $ NotAValidPatternVariable r p k
      _ -> throwError $ OutOfScope (getRange p) p
    t <- during (PushTermElaboration t) $ stm (valueDesc stk) t
    a <- sact a
    pure $ Push r (judgementName jd) (p, valueDesc stk, t) a

  Lookup r rt@t (av, a) b -> do
    (jd, stk) <- asks currentActor >>= \case
      (jd, Nothing) -> throwError (LookupFromAStacklessActor r jd)
      (jd, Just stk) -> pure (jd, stk)
    t <- during (LookupTermElaboration t) $ stm (keyDesc stk) t
    av <- traverse isFresh av
    ovs <- asks objVars
    (a, mcha) <- local (declare av (ActVar (Known $ valueDesc stk) ovs)) $ sbranch a
    (b, mchb) <- sbranch b
    during (LookupHandlersElaboration rt) $ consistentCommunication [mcha, mchb]
    pure $ Lookup r t (ActorMeta <$> av, a) b

  Fail r fmt -> Fail r <$> sformat fmt <* tell (All False)
  Print r fmt a -> Print r <$> sformat fmt <*> sact a
  Break r fmt a -> Break r <$> sformat fmt <*> sact a
  Note r a -> Note r <$> sact a

sformat :: [Format Directive Debug Raw] -> Elab [Format Directive Debug ACTm]
sformat fmt = do
  desc <- fromInfo Unknown
  traverse (traverse $ stm desc) fmt

consistentCommunication :: [Maybe ElabState] -> Elab ()
consistentCommunication sts = do
 case List.groupBy ((==) `on` fmap snd . channelStates) [ p | Just p <- sts ] of
   [] -> tell (All False) -- all branches are doomed, we don't care
   [(c:_)] -> put c
   _ -> throwError InconsistentCommunication

sbranch :: CActor -> Elab (AActor, Maybe ElabState)
sbranch ra = do
  chs <- get
  (a, All b) <- censor (const (All True)) $ listen $ sact ra
  chs' <- get
  unless b $ unless (chs == chs') $ throwError (DoomedBranchCommunicated ra)
  put chs
  pure (a, chs' <$ guard b)

sclause :: SyntaxDesc -> (RawP, CActor) ->
           Elab ((Pat, AActor), Maybe ElabState)
sclause desc (rp, a) = during (MatchBranchElaboration rp) $ do
  (p, ds, hs) <- spat desc rp
  (a, me) <- local (setDecls ds . setHints hs) $ sbranch a
  pure ((p, a), me)

sprotocol :: CProtocol -> Elab AProtocol
sprotocol ps = during (ProtocolElaboration ps) $ do
  syndecls <- gets (Map.keys . syntaxCats)
  traverse (traverse (ssyntaxdecl syndecls)) ps

sjudgementstack :: CJudgementStack -> Elab AJudgementStack
sjudgementstack (JudgementStack key val) = do
  syndecls <- gets (Map.keys . syntaxCats)
  key <- ssyntaxdecl syndecls key
  val <- ssyntaxdecl syndecls val
  pure (JudgementStack key val)
