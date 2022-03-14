module Elaboration where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Function
import Data.List (isPrefixOf, groupBy)
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

import Bwd
import Format
import Hide
import Scope
import Syntax
import Thin
import Utils

import Concrete.Base (Variable(..), Raw(..), SbstC(..), RawP(..), ThDirective(..))
import qualified Concrete.Base as C

import Term.Base
import Term.Substitution
import Pattern as P
import Actor (ActorMeta(..), Channel(..))
import qualified Actor as A

data Mode = Input | {- Subject | -} Output
  deriving (Show, Eq)

type Protocol = [(Mode, SyntaxCat)]

data JudgementStack t = JudgementStack
  { keyCat :: SyntaxCat
  , valueDesc :: t
  } deriving (Show)

dual :: Protocol -> Protocol
dual = map $ \case
  (Input, c) -> (Output, c)
  (Output, c) -> (Input, c)

data Info a = Unknown | Known a | Inconsistent
  deriving (Show, Eq)

instance Eq a => Monoid (Info a) where
  mempty = Unknown
  Unknown `mappend` y = y
  x `mappend` Unknown = x
  Known x `mappend` Known y | x == y = Known x
  _ `mappend` _ = Inconsistent

instance Eq a => Semigroup (Info a) where
  (<>) = mappend

compatibleInfos :: Info SyntaxCat -> Info SyntaxCat -> Elab ()
compatibleInfos cat cat' =
  when (cat <> cat' == Inconsistent) $
    throwError (IncompatibleSyntaxCats cat cat')

type ObjVar = (String, Info SyntaxCat)
type ObjVars = Bwd ObjVar

data Kind
  = ActVar (Info SyntaxCat) ObjVars
  | AChannel ObjVars
  | AJudgement (Maybe (JudgementStack SyntaxDesc)) Protocol
  deriving (Show)

type Hints = Map String (Info SyntaxCat)

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

declare :: String -> Kind -> Context -> Context
declare x k ctx = ctx { declarations = declarations ctx :< (x, k) }

turn :: Turn -> Context -> Context
turn t ds = ds { location = location ds :< t }

setDecls :: Decls -> Context -> Context
setDecls ds ctx = ctx { declarations = ds }

setHints :: Hints -> Context -> Context
setHints hs ctx = ctx { binderHints = hs }

type Decls = Bwd (String, Kind)
type Slced = [(String, Kind)]
type Focus a = (Decls, a, Slced)

resolve :: Variable -> Elab (Maybe (Either Kind (Info SyntaxCat, DB)))
resolve (Variable x) = do
  ctx <- ask
  let ds  = declarations ctx
  let ovs = objVars ctx
  case focusBy (\ (y, k) -> k <$ guard (x == y)) ds of
    Just (_, k, _) -> pure (Just $ Left k)
    _ -> case focusBy (\ (y, cat) -> cat <$ guard (x == y)) ovs of
      Just (xz, cat, xs) -> pure (Just $ Right (cat, DB $ length xs))
      Nothing -> pure Nothing

isFresh :: Variable -> Elab String
isFresh x = do
  res <- resolve x
  whenJust res $ \ _ -> throwError (VariableShadowing x)
  pure (getVariable x)

data Complaint
  -- scope
  = OutOfScope Variable
  | MetaScopeTooBig Variable ObjVars ObjVars
  | VariableShadowing Variable
  | EmptyContext
  | NotTopVariable Variable Variable
  -- kinding
  | NotAValidTermVariable Variable Kind
  | NotAValidPatternVariable Variable Kind
  | NotAValidJudgement Variable (Maybe Kind)
  | NotAValidChannel Variable (Maybe Kind)
  | NotAValidBoundVar Variable
  -- protocol
  | InvalidSend Channel
  | InvalidRecv Channel
  | NonLinearChannelUse Channel
  | UnfinishedProtocol Channel Protocol
  | InconsistentCommunication
  | DoomedBranchCommunicated C.Actor
  -- judgement stacks
  | PushingOnAStacklessJudgement A.JudgementForm
  -- syntaxes
  | NotAValidSyntaxCat SyntaxCat
  | AlreadyDeclaredSyntaxCat SyntaxCat
  | SyntaxContainsMeta SyntaxCat
  | InvalidSyntax SyntaxCat
  -- syntaxdesc validation
  | InconsistentSyntaxCat
  | InvalidSyntaxDesc SyntaxDesc
  | IncompatibleSyntaxCats (Info SyntaxCat) (Info SyntaxCat)
  | ExpectedNilGot String
  | ExpectedEnumGot [String] String
  | ExpectedTagGot [String] String
  | ExpectedANilGot Raw
  | ExpectedANilPGot RawP
  | ExpectedAConsGot Raw
  | ExpectedAConsPGot RawP
  | SyntaxError SyntaxDesc Raw
  | SyntaxPError SyntaxDesc RawP
  -- contextual info
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
  | DeclaringSyntaxCat SyntaxCat Complaint
  | SubstitutionElaboration (Bwd SbstC) Complaint
  | PatternVariableElaboration Variable Complaint
  | TermVariableElaboration Variable Complaint
  deriving (Show)

data ElabState = ElabState
  { channelStates :: Map Channel ([Turn], Protocol)
  , syntaxCats    :: Map SyntaxCat SyntaxDesc
  } deriving (Eq)

isSyntaxCat :: String -> Elab SyntaxCat
isSyntaxCat str = do
  cats <- gets syntaxCats
  case Map.lookup str cats of
    Nothing -> throwError (NotAValidSyntaxCat str)
    Just _ -> pure str

addHint :: String -> Info SyntaxCat -> Context -> Context
addHint str cat ctx =
  let hints = binderHints ctx
      hints' = case Map.lookup str hints of
                 Nothing -> Map.insert str cat hints
                 Just cat' -> Map.insert str (cat <> cat') hints
  in ctx { binderHints = hints' }

getHint :: String -> Elab (Info SyntaxCat)
getHint str = do
  hints <- asks binderHints
  pure $ fromMaybe Unknown $ Map.lookup str hints

fromInfo :: Info SyntaxCat -> Elab SyntaxDesc
fromInfo Unknown = pure (("Term", 0) #% [])
fromInfo (Known cat) = pure (("Rec", 0) #% [atom cat 0])
fromInfo Inconsistent = throwError InconsistentSyntaxCat

declareSyntax :: SyntaxCat -> SyntaxDesc -> Elab ()
declareSyntax cat desc = do
  st <- get
  whenJust (Map.lookup cat (syntaxCats st)) $ \ _ ->
    throwError (AlreadyDeclaredSyntaxCat cat)
  put (st { syntaxCats = Map.insert cat desc (syntaxCats st) })

channelLookup :: Channel -> ElabState -> Maybe ([Turn], Protocol)
channelLookup ch = Map.lookup ch . channelStates

channelInsert :: Channel -> ([Turn], Protocol) -> ElabState -> ElabState
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

svar :: Variable -> Elab (Info SyntaxCat, ACTm)
svar x = do
  ovs <- asks objVars
  res <- resolve x
  case res of
    Just (Left k) -> case k of -- TODO: come back and remove fst <$>
      ActVar cat sc -> case findSub (fst <$> sc) (fst <$> ovs) of
        Just th -> pure (cat, ActorMeta (getVariable x) $: sbstW (sbst0 0) th)
        Nothing -> throwError (MetaScopeTooBig x sc ovs)
      _ -> throwError (NotAValidTermVariable x k)
    Just (Right (cat, i)) -> pure (cat, var i (length ovs))
    Nothing -> throwError (OutOfScope x)

getName :: Elab [Turn]
getName = do
  loc <- asks location
  pure (loc <>> [])

spop :: Elab (ObjVars, (Variable, Info SyntaxCat))
spop = do
  ovs <- asks objVars
  case ovs of
    B0 -> throwError EmptyContext
    (xz :< (x, cat)) -> pure (xz, (Variable x, cat))

ssbst :: Bwd SbstC -> Elab (ACTSbst, ObjVars)
ssbst B0 = do
    ovs <- asks objVars
    pure (sbstI (length ovs), ovs)
ssbst (sg :< sgc) = case sgc of
    Keep v -> do
      (xz, (w, cat)) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst sg)
      pure (sbstW sg (ones 1), ovs :< (getVariable w, cat))
    Drop v -> do
      (xz, (w, cat)) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst sg)
      pure (weak sg, ovs)
    Assign v t -> do
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

isRec :: SyntaxDesc -> Maybe (Info SyntaxCat)
isRec = asTagged $ \case
  ("Rec", _) -> asPair $ asAtom $ \ (at, _) _ -> pure (Known at)
  _ -> bust

stms :: [SyntaxDesc] -> Raw -> Elab ACTm
stms [] (At "") = atom "" <$> asks (length . objVars)
stms [] (At a) = throwError (ExpectedNilGot a)
stms [] t = throwError (ExpectedANilGot t)
stms (d:ds) (Cons p q) = (%) <$> stm d p <*> stms ds q
stms _ t = throwError (ExpectedAConsGot t)

stm :: SyntaxDesc -> Raw -> Elab ACTm
stm desc (Var v) = do
  table <- gets syntaxCats
  (cat, t) <- svar v
  case isRec desc of
    Nothing -> case Syntax.expand table desc of
      Just VTerm -> pure ()
      _ -> throwError (SyntaxError desc (Var v))
    Just cat' -> during (TermVariableElaboration v) $ compatibleInfos cat cat'
  pure t
stm desc (Sbst sg t) = do
    (sg, ovs) <- during (SubstitutionElaboration sg) $ ssbst sg
    t <- local (setObjVars ovs) (stm desc t)
    pure (t //^ sg)
stm desc rt = do
  table <- gets syntaxCats
  case Syntax.expand table desc of
    Nothing -> throwError (InvalidSyntaxDesc desc)
    Just vdesc -> case rt of
      At a -> do
        case vdesc of
          VAtom -> pure ()
          VNil -> unless (a == "") $ throwError (ExpectedNilGot a)
          VNilsOrCons{} -> unless (a == "") $ throwError (ExpectedNilGot a)
          VEnum ts -> unless (a `elem` ts) $ throwError (ExpectedEnumGot ts a)
          VTerm -> pure ()
          _ -> throwError (SyntaxError desc rt)
        atom a <$> asks (length . objVars)
      Cons p q -> case vdesc of
        VNilsOrCons d1 d2 -> (%) <$> stm d1 p <*> stm d2 q
        VCons d1 d2 -> (%) <$> stm d1 p <*> stm d2 q
        VTerm -> (%) <$> stm desc p <*> stm desc q
        VTag ds -> case p of
          At a -> case lookup a ds of
            Nothing -> throwError (ExpectedTagGot (fst <$> ds) a)
            Just descs -> (%) <$> stm (("Atom", 0) #% []) p <*> stms descs q
          _ -> throwError (SyntaxError desc rt)
        _ -> throwError (SyntaxError desc rt)
      Lam (Scope (Hide x) sc) -> (x \\) <$> do
        (s, desc) <- case vdesc of
          VTerm -> pure (Unknown, desc)
          VBind cat desc -> pure (Known cat, desc)
          _ -> throwError (SyntaxError desc rt)
        x <- isFresh (Variable x)
        local (declareObjVar (x, s)) $ stm desc sc

spats :: [SyntaxDesc] -> RawP -> Elab (Pat, Decls, Hints)
spats [] (AtP "") = (AP "",,) <$> asks declarations <*> asks binderHints
spats [] (AtP a) = throwError (ExpectedNilGot a)
spats [] t = throwError (ExpectedANilPGot t)
spats (d:ds) (ConsP p q) = do
  (p, decls, hints) <- spat d p
  (q, decls, hints) <- local (setDecls decls . setHints hints) $ spats ds q
  pure (PP p q, decls, hints)
spats _ t = throwError (ExpectedAConsPGot t)

spat :: SyntaxDesc -> RawP -> Elab (Pat, Decls, Hints)
spat desc (C.VarP v) = do
  table <- gets syntaxCats
  cat <- case isRec desc of
    Nothing -> case Syntax.expand table desc of
      Just VTerm -> pure Unknown
      _ -> throwError (SyntaxPError desc (VarP v))
    Just cat -> pure cat
  ds <- asks declarations
  hs <- asks binderHints
  res <- resolve v
  case res of
    Just (Left k)  -> throwError (NotAValidPatternVariable v k)
    Just (Right (cat', i)) -> do
      during (PatternVariableElaboration v) $ compatibleInfos cat cat'
      pure (VP i, ds, hs)
    Nothing -> do
      ovs <- asks objVars
      v <- pure (getVariable v)
      pure (MP v (ones (length ovs)), ds :< (v, ActVar cat ovs), hs)
spat desc (ThP th p) = do
  th <- sth th
  (p, ds, hs) <- local (th ^?) $ spat desc p
  pure (p *^ th, ds, hs)
spat desc UnderscoreP = (HP,,) <$> asks declarations <*> asks binderHints
spat desc rp = do
  table <- gets syntaxCats
  case Syntax.expand table desc of
    Nothing -> throwError (InvalidSyntaxDesc desc)
    Just vdesc -> case rp of
      AtP a -> do
        case vdesc of
          VAtom -> pure ()
          VNil -> unless (a == "") $ throwError (ExpectedNilGot a)
          VNilsOrCons{} -> unless (a == "") $ throwError (ExpectedNilGot a)
          VEnum ts -> unless (a `elem` ts) $ throwError (ExpectedEnumGot ts a)
          VTerm -> pure ()
          _ -> throwError (SyntaxPError desc rp)
        (AP a,,) <$> asks declarations <*> asks binderHints

      ConsP p q -> case vdesc of
        VNilsOrCons d1 d2 -> do
          (p, ds, hs) <- spat d1 p
          (q, ds, hs) <- local (setDecls ds . setHints hs) (spat d2 q)
          pure (PP p q, ds, hs)
        VCons d1 d2 -> do
          (p, ds, hs) <- spat d1 p
          (q, ds, hs) <- local (setDecls ds . setHints hs) (spat d2 q)
          pure (PP p q, ds, hs)
        VTerm -> do
          (p, ds, hs) <- spat desc p
          (q, ds, hs) <- local (setDecls ds . setHints hs) (spat desc q)
          pure (PP p q, ds, hs)
        VTag ds -> case p of
          AtP a -> case lookup a ds of
            Nothing -> throwError (ExpectedTagGot (fst <$> ds) a)
            Just descs ->  do
              (p, ds, hs) <- spat (("Atom", 0) #% []) p
              (q, ds, hs) <- local (setDecls ds . setHints hs) (spats descs q)
              pure (PP p q, ds, hs)
          _ -> throwError (SyntaxPError desc rp)
        _ -> throwError (SyntaxPError desc rp)

      LamP (Scope v@(Hide x) p) -> do
        (s, desc) <- case vdesc of
          VTerm -> pure (Unknown, desc)
          VBind cat desc -> pure (Known cat, desc)
          _ -> throwError (SyntaxPError desc rp)

        () <$ isFresh (Variable x)
        (p, ds, hs) <- local (declareObjVar (x, s) . addHint x s) $ spat desc p
        pure (BP v p, ds, hs)

isChannel :: Variable -> Elab Channel
isChannel ch = resolve ch >>= \case
  Just (Left (AChannel sc)) -> pure (Channel $ getVariable ch)
  Just mk -> throwError (NotAValidChannel ch $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope ch)

isJudgement :: Variable -> Elab (A.JudgementForm, Maybe (JudgementStack SyntaxDesc), Protocol)
isJudgement jd = resolve jd >>= \case
  Just (Left (AJudgement mstk p)) -> pure (getVariable jd, mstk, p)
  Just mk -> throwError (NotAValidJudgement jd $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope jd)

channelScope :: Channel -> Elab ObjVars
channelScope (Channel ch) = do
  ds <- asks declarations
  case fromJust (focusBy (\ (y, k) -> k <$ guard (ch == y)) ds) of
    (_, AChannel sc, _) -> pure sc

steppingChannel :: Channel -> (Protocol -> Elab (SyntaxCat, Protocol)) ->
                   Elab SyntaxCat
steppingChannel ch step = do
  nm <- getName
  (pnm, p) <- gets (fromJust . channelLookup ch)
  unless (pnm `isPrefixOf` nm) $ throwError (NonLinearChannelUse ch)
  (cat, p) <- step p
  modify (channelInsert ch (nm, p))
  pure cat

open :: Channel -> Protocol -> Elab ()
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

withChannel :: Channel -> Protocol -> Elab a -> Elab a
withChannel ch@(Channel rch) p ma = do
  open ch p
  -- run the actor in the extended context
  ovs <- asks objVars
  a <- local (declare rch (AChannel ovs)) $ ma
  close ch
  pure a

guessCat :: Raw -> Elab (Info SyntaxCat)
guessCat (Var v) = resolve v >>= \case
  Just (Right (info, i)) -> pure info
  Just (Left (ActVar info _)) -> pure info
  _ -> pure Unknown
guessCat _ = pure Unknown

sact :: C.Actor -> Elab A.Actor
sact = \case
  C.Win -> pure A.Win
  C.Constrain s t -> do
    infoS <- guessCat s
    infoT <- guessCat t
    desc <- during (ConstrainSyntaxCatGuess s t) $ fromInfo (infoS <> infoT)
    s <- during (ConstrainTermElaboration s) $ stm desc s
    t <- during (ConstrainTermElaboration t) $ stm desc t
    pure $ A.Constrain s t

  a C.:|: b -> do
    a <- local (turn West) $ sact a
    b <- local (turn East) $ sact b
    pure (a A.:|: b)

  C.Spawn jd ch a -> do
    -- check the channel name is fresh & initialise it
    ch <- Channel <$> isFresh ch
    (jd, _, p) <- isJudgement jd

    a <- withChannel ch (dual p) $ sact a

    pure $ A.Spawn jd ch a

  C.Send ch tm a -> do
    ch <- isChannel ch
    -- Check the channel is in sending mode, & step it
    cat <- steppingChannel ch $ \case
      (Output, cat) : p -> pure (cat, p)
      _ -> throwError (InvalidSend ch)

    -- Send
    tm <- during (SendTermElaboration ch tm) $ do
      sc <- channelScope ch
      ovs <- asks objVars
      let (thx, xyz, thy) = lintersection sc ovs
      desc <- fromInfo (Known cat)
      (*^ thx) <$> local (setObjVars xyz) (stm desc tm)

    a <- sact a
    pure $ A.Send ch tm a

  C.Recv ch (av, a) -> do
    ch <- isChannel ch
    av <- during (RecvMetaElaboration ch) $ isFresh av
    -- Check the channel is in receiving mode & step it
    cat <- steppingChannel ch $ \case
      (Input, cat) : p -> pure (cat, p)
      _ -> throwError (InvalidRecv ch)

    -- Receive
    sc <- channelScope ch
    a <- local (declare av (ActVar (Known cat) sc)) $ sact a
    pure $ A.Recv ch (ActorMeta av, a)

  C.FreshMeta cat (av, a) -> do
    cat <- during FreshMetaElaboration $ isSyntaxCat cat
    av <- during FreshMetaElaboration $ isFresh av
    ovs <- asks objVars
    a <- local (declare av (ActVar (Known cat) ovs)) $ sact a
    pure $ A.FreshMeta cat (ActorMeta av, a)

  C.Under (Scope v@(Hide x) a) -> do
    during UnderElaboration $ () <$ isFresh (Variable x)
    a <- local (declareObjVar (x, Unknown)) $ sact a
    pure $ A.Under (Scope v a)

  C.Match rtm@tm cls -> do
    desc <- fromInfo =<< guessCat rtm
    tm <- during (MatchTermElaboration tm) $ stm desc tm
    chs <- get
    clsts <- traverse (sclause desc) cls
    let (cls, sts) = unzip clsts
    during (MatchElaboration rtm) $ consistentCommunication sts
    pure $ A.Match tm cls

  C.Push jd (p, t) a -> do
    (jd, mstk, _) <- isJudgement jd
    stk <- case mstk of
      Nothing -> throwError (PushingOnAStacklessJudgement jd)
      Just stk -> pure stk

    p <- resolve p >>= \case
      Just (Right (cat, i)) -> i <$ compatibleInfos cat (Known $ keyCat stk)
      Just (Left k) -> throwError $ NotAValidPatternVariable p k
      _ -> throwError $ OutOfScope p
    t <- during (PushTermElaboration t) $ stm (valueDesc stk) t
    a <- sact a
    pure $ A.Push jd (p, t) a

  C.Lookup rt@t (av, a) b -> do
    desc <- fromInfo Unknown
    t <- during (LookupTermElaboration t) $ stm desc t
    av <- isFresh av
    ovs <- asks objVars
    (a, mcha) <- local (declare av (ActVar Unknown ovs)) $ sbranch a
    (b, mchb) <- sbranch b
    during (LookupHandlersElaboration rt) $ consistentCommunication [mcha, mchb]
    pure $ A.Lookup t (ActorMeta av, a) b

  C.Fail fmt -> A.Fail <$> sformat fmt <* tell (All False)
  C.Print fmt a -> A.Print <$> sformat fmt <*> sact a
  C.Break fmt a -> A.Break <$> sformat fmt <*> sact a

sformat :: [Format Directive Debug Raw] -> Elab [Format Directive Debug ACTm]
sformat fmt = do
  desc <- fromInfo Unknown
  traverse (traverse $ stm desc) fmt

consistentCommunication :: [Maybe ElabState] -> Elab ()
consistentCommunication sts = do
 case groupBy ((==) `on` fmap snd . channelStates) [ p | Just p <- sts ] of
   [] -> tell (All False) -- all branches are doomed, we don't care
   [(c:_)] -> put c
   _ -> throwError InconsistentCommunication

sbranch :: C.Actor -> Elab (A.Actor, Maybe ElabState)
sbranch ra = do
  chs <- get
  (a, All b) <- censor (const (All True)) $ listen $ sact ra
  chs' <- get
  unless b $ unless (chs == chs') $ throwError (DoomedBranchCommunicated ra)
  put chs
  pure (a, chs' <$ guard b)

sclause :: SyntaxDesc -> (RawP, C.Actor) ->
           Elab ((Pat, A.Actor), Maybe ElabState)
sclause desc (rp, a) = during (MatchBranchElaboration rp) $ do
  (p, ds, hs) <- spat desc rp
  (a, me) <- local (setDecls ds . setHints hs) $ sbranch a
  pure ((p, a), me)
