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
import Data.List.NonEmpty (NonEmpty, fromList)

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

type ObjVar = (String, Info SyntaxDesc)
type ObjVars = Bwd ObjVar

data Kind
  = ActVar (Info SyntaxDesc) ObjVars
  | AChannel ObjVars
  | AJudgement ExtractMode AProtocol
  | AStack AContextStack
  deriving (Show)

type Hints = Map String (Info SyntaxDesc)

data Context = Context
  { objVars      :: ObjVars
  , declarations :: Decls
  , location     :: Bwd Turn
  , binderHints  :: Hints
  } deriving (Show)

initContext :: Context
initContext = Context B0 B0 B0 Map.empty

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

data Warning
  = UnreachableClause Range RawP
  | MissingClauses Range (NonEmpty RawP)

instance HasGetRange Warning where
  getRange = \case
    UnreachableClause r _ -> r
    MissingClauses r _ -> r

raiseWarning :: Warning -> Elab ()
raiseWarning w = do
  modify (\ r -> r { warnings = warnings r :< w })

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

type ChannelStates = Map Channel ([Turn], AProtocol)

data ElabState = ElabState
  { channelStates :: ChannelStates
  , syntaxCats    :: SyntaxTable
  , warnings      :: Bwd Warning
  }

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

fromInfo :: Range -> Info SyntaxDesc -> Elab SyntaxDesc
fromInfo r Unknown = pure (atom "Wildcard" 0)
fromInfo r (Known desc) = pure desc
-- I believe this last case is currently unreachable because this
-- may only arise from a call to (<>) and this is only used in two
-- places:
-- 1. `addHint` (and if we had a clash, that'd be a shadowing error)
-- 2. `compatibleInfos` where the error is handled locally
fromInfo r Inconsistent = throwError (InconsistentSyntaxDesc r)

declareSyntax :: WithRange SyntaxCat -> SyntaxDesc -> Elab ()
declareSyntax (WithRange r cat) desc = do
  st <- get
  whenJust (Map.lookup cat (syntaxCats st)) $ \ _ ->
    throwError (AlreadyDeclaredSyntaxCat r cat)
  put (st { syntaxCats = Map.insert cat desc (syntaxCats st) })

channelLookup :: Channel -> ElabState -> Maybe ([Turn], AProtocol)
channelLookup ch = Map.lookup ch . channelStates

channelInsert :: Channel -> ([Turn], AProtocol) -> ElabState -> ElabState
channelInsert ch x st = st { channelStates = Map.insert ch x (channelStates st) }

channelDelete :: Channel -> ElabState -> ElabState
channelDelete ch st = st { channelStates = Map.delete ch (channelStates st) }

initElabState :: ElabState
initElabState = ElabState Map.empty Map.empty B0

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
      desc <- fromInfo r info
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
  compatibleInfos (getRange v) (Known desc) desc'
  pure t
stm desc (Sbst r sg t) = do
    (sg, ovs) <- during (SubstitutionElaboration sg) $ ssbst sg
    t <- local (setObjVars ovs) (stm desc t)
    pure (t //^ sg)
stm desc rt = do
  table <- gets syntaxCats
  case Syntax.expand table desc of
    Nothing -> throwError (InvalidSyntaxDesc (getRange rt) desc)
    Just vdesc -> case rt of
      At r a -> do
        case vdesc of
          VAtom -> pure ()
          VAtomBar as -> when (a `elem` as) $ throwError (GotBarredAtom r a as)
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

-- Returns:
-- 1. Elaborated pattern
-- 2. Bound variables (together with their syntactic categories)
-- 3. Binder hints introduced by \x. patterns
spat :: SyntaxDesc -> RawP -> Elab (Pat, Decls, Hints)
spat desc (AsP r v p) = do
  v <- isFresh v
  ds <- asks declarations
  ovs <- asks objVars
  (p, ds, hs) <- local (setDecls (ds :< (v, ActVar (Known desc) ovs))) $ spat desc p
  pure (AT v p, ds, hs)
spat desc (VarP r v) = during (PatternVariableElaboration v) $ do
  table <- gets syntaxCats
  ds <- asks declarations
  hs <- asks binderHints
  res <- resolve v
  case res of
    Just (Left k)  -> throwError (NotAValidPatternVariable r v k)
    Just (Right (desc', i)) -> do
      compatibleInfos (getRange v) (Known desc) desc'
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
    Nothing -> throwError (InvalidSyntaxDesc (getRange rp) desc)
    Just vdesc -> case rp of
      AtP r a -> do
        case vdesc of
          VAtom -> pure ()
          VAtomBar as -> when (a `elem` as) $ throwError (GotBarredAtom r a as)
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
  , judgementProtocol :: AProtocol
  }

isJudgement :: Variable -> Elab IsJudgement
isJudgement jd = resolve jd >>= \case
  Just (Left (AJudgement em p)) -> pure (IsJudgement em (getVariable jd) p)
  Just mk -> throwError (NotAValidJudgement (getRange jd) jd $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope (getRange jd) jd)

isContextStack :: Variable -> Elab (Stack, AContextStack)
isContextStack stk = resolve stk >>= \case
  Just (Left (AStack stkTy)) -> pure (Stack (getVariable stk), stkTy)
  Just mk -> throwError (NotAValidStack (getRange stk) stk $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope (getRange stk) stk)


channelScope :: Channel -> Elab ObjVars
channelScope (Channel ch) = do
  ds <- asks declarations
  case fromJust (focusBy (\ (y, k) -> k <$ guard (ch == y)) ds) of
    (_, AChannel sc, _) -> pure sc

steppingChannel :: Range -> Channel -> (AProtocol -> Elab (a, AProtocol)) ->
                   Elab a
steppingChannel r ch step = do
  nm <- getName
  (pnm, p) <- gets (fromJust . channelLookup ch)
  unless (pnm `isPrefixOf` nm) $ throwError (NonLinearChannelUse r ch)
  (cat, p) <- step p
  modify (channelInsert ch (nm, p))
  pure cat

open :: Channel -> AProtocol -> Elab ()
open ch p = do
  nm <- getName
  modify (channelInsert ch (nm, p))

close :: Range -> Channel -> Elab ()
close r ch = do
  -- make sure the protocol was run all the way
  mp <- gets (channelLookup ch)
  case snd (fromJust mp) of
    [] -> pure ()
    p -> throwError (UnfinishedProtocol r ch p)
  modify (channelDelete ch)

withChannel :: Range -> Channel -> AProtocol -> Elab a -> Elab a
withChannel r ch@(Channel rch) p ma = do
  open ch p
  -- run the actor in the extended context
  ovs <- asks objVars
  a <- local (declare (Used rch) (AChannel ovs)) $ ma
  close r ch
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

sirrefutable :: String -> RawP -> Elab (Binder String, Maybe (Raw, RawP))
sirrefutable nm = \case
  VarP _ v -> (, Nothing) . Used <$> isFresh v
  UnderscoreP _ -> pure (Unused ,Nothing)
  p -> do ctxt <- ask
          -- this should be a unique name & is not user-writable
          let r = getRange p
          let av = "$" ++ nm ++ show (length (objVars ctxt) + length (declarations ctxt))
          pure (Used av, Just (Var r (Variable r av), p))

sact :: CActor -> Elab AActor
sact = \case
  Win r -> pure (Win r)
  Constrain r s t -> do
    infoS <- guessDesc False s
    infoT <- guessDesc False t
    desc <- during (ConstrainSyntaxCatGuess s t) $
      fromInfo r =<< compatibleInfos r infoS infoT
    s <- during (ConstrainTermElaboration s) $ stm desc s
    t <- during (ConstrainTermElaboration t) $ stm desc t
    pure $ Constrain r s t

  Branch r a b -> do
    a <- local (turn West) $ sact a
    b <- local (turn East) $ sact b
    pure (Branch r a b)

  Spawn r em jd ch a -> do
    let rp = getRange jd <> getRange ch
    -- check the channel name is fresh & initialise it
    ch <- Channel <$> isFresh ch
    jd <- isJudgement jd

    a <- withChannel rp ch (dual $ judgementProtocol jd) $ sact a

    em <- pure $ case em of
      AlwaysExtract -> judgementExtract jd
      _ -> em

    pure $ Spawn r em (judgementName jd) ch a

  Send r ch tm a -> do
    ch <- isChannel ch
    -- Check the channel is in sending mode, & step it
    desc <- steppingChannel r ch $ \case
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

  Recv r ch (p, a) -> do
    ch <- isChannel ch
    (av, pat) <- during (RecvMetaElaboration ch) $ sirrefutable "recv" p

    -- Check the channel is in receiving mode & step it
    cat <- steppingChannel r ch $ \case
      (Input, cat) : p -> pure (cat, p)
      _ -> throwError (InvalidRecv r ch av)

    -- Receive
    sc <- channelScope ch
    a <- local (declare av (ActVar (Known cat) sc)) $ sact $ case pat of
      Nothing -> a
      Just (var, p) -> Match r var [(p, a)]
    pure $ Recv r ch (ActorMeta <$> av, a)

  Connect r (CConnect ch1 ch2) -> during (ConnectElaboration ch1 ch2) $ do
    ch1 <- isChannel ch1
    ch2 <- isChannel ch2
    p <- steppingChannel r ch1 $ \ p -> pure (p, [])
    q <- steppingChannel r ch2 $ \ p -> pure (p, [])
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

  Let r av desc t a -> do
    (desc, av, ovs) <- during FreshMetaElaboration $ do
      syndecls <- gets (Map.keys . syntaxCats)
      desc <- ssyntaxdecl syndecls desc
      av <- isFresh av
      ovs <- asks objVars
      pure (desc, av, ovs)
    t <- stm desc t
    a <- local (declare (Used av) (ActVar (Known desc) ovs)) $ sact a
    pure (Let r (ActorMeta av) desc t a)

  Under r (Scope v@(Hide x) a) -> do
    during UnderElaboration $ () <$ isFresh x
    a <- local (declareObjVar (getVariable x, Unknown)) $ sact a
    pure $ Under r (Scope v a)

  Match r rtm@tm cls -> do
    desc <- fromInfo (getRange rtm) =<< guessDesc False rtm
    tm <- during (MatchTermElaboration tm) $ stm desc tm
    chs <- get
    (clsts, cov) <- traverse (sclause desc) cls `runStateT` [desc]
    unless (null cov) $ do
      table <- gets syntaxCats
      let examples = fromList cov >>= missing table
      raiseWarning $ MissingClauses r examples
    let (cls, sts) = unzip clsts
    during (MatchElaboration rtm) $ consistentCommunication r sts
    pure $ Match r tm cls

  Push r stk (p, (), t) a -> do
    (stk, stkTy) <- isContextStack stk

    p <- resolve p >>= \case
      Just (Right (cat, i)) -> i <$ compatibleInfos (getRange p) cat (Known $ keyDesc stkTy)
      Just (Left k) -> throwError $ NotAValidPatternVariable r p k
      _ -> throwError $ OutOfScope (getRange p) p
    t <- during (PushTermElaboration t) $ stm (valueDesc stkTy) t
    a <- sact a
    pure $ Push r stk (p, valueDesc stkTy, t) a

  Lookup r rt@t stk (p, a) b -> do
    (stk, stkTy) <- isContextStack stk
    t <- during (LookupTermElaboration t) $ stm (keyDesc stkTy) t
    (av, mpat) <- sirrefutable "lookup" p
    ovs <- asks objVars
    (a, mcha) <- local (declare av (ActVar (Known $ valueDesc stkTy) ovs))
                 $ sbranch $ case mpat of
                    Nothing -> a
                    Just (var, pat) -> Match r var [(pat, a)]
    (b, mchb) <- sbranch b
    during (LookupHandlersElaboration rt) $
      consistentCommunication r [mcha, mchb]
    pure $ Lookup r t stk (ActorMeta <$> av, a) b

  Fail r fmt -> Fail r <$> sformat fmt <* tell (All False)
  Print r fmt a -> Print r <$> sformat fmt <*> sact a
  Break r fmt a -> Break r <$> sformat fmt <*> sact a
  Note r a -> Note r <$> sact a

sformat :: [Format Directive Debug Raw] -> Elab [Format Directive Debug ACTm]
sformat fmt = do
  desc <- fromInfo unknown Unknown
  traverse (traverse $ stm desc) fmt

consistentCommunication :: Range -> [Maybe ChannelStates] -> Elab ()
consistentCommunication r sts = do
 case List.groupBy ((==) `on` fmap snd) [ p | Just p <- sts ] of
   [] -> tell (All False) -- all branches are doomed, we don't care
   [(c:_)] -> modify (\ r -> r { channelStates = c })
   _ -> throwError (InconsistentCommunication r)

sbranch :: CActor -> Elab (AActor, Maybe ChannelStates)
sbranch ra = do
  chs <- gets channelStates
  (a, All b) <- censor (const (All True)) $ listen $ sact ra
  st <- get
  unless b $ unless (chs == channelStates st) $
    throwError (DoomedBranchCommunicated (getRange ra) ra)
  put (st { channelStates = chs })
  pure (a, channelStates st <$ guard b)

sclause :: SyntaxDesc -> (RawP, CActor) ->
           StateT [SyntaxDesc] Elab ((Pat, AActor), Maybe ChannelStates)
sclause desc (rp, a) = do
  (p, ds, hs) <- lift $ during (MatchBranchElaboration rp) $ spat desc rp
  leftovers <- get
  table <- lift $ gets syntaxCats
  leftovers <- lift $ case combine' $ map (\ d -> (d, shrinkBy table d p)) leftovers of
    Covering -> pure []
    AlreadyCovered -> do
      raiseWarning (UnreachableClause (getRange rp) rp)
      pure leftovers
    PartiallyCovering _ ps -> pure ps
  put leftovers
  (a, me) <- lift $ during (MatchBranchElaboration rp) $
               local (setDecls ds . setHints hs) $ sbranch a
  pure ((p, a), me)

sprotocol :: CProtocol -> Elab AProtocol
sprotocol ps = during (ProtocolElaboration ps) $ do
  syndecls <- gets (Map.keys . syntaxCats)
  traverse (traverse (ssyntaxdecl syndecls)) ps

scontextstack :: CContextStack -> Elab AContextStack
scontextstack (ContextStack key val) = do
  syndecls <- gets (Map.keys . syntaxCats)
  key <- ssyntaxdecl syndecls key
  val <- ssyntaxdecl syndecls val
  pure (ContextStack key val)
