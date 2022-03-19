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

type Protocol t = [(Mode, t)]

data JudgementStack t = JudgementStack
  { keyDesc :: t
  , valueDesc :: t
  } deriving (Show)

type CProtocol = Protocol C.Raw
type AProtocol = Protocol SyntaxDesc

type CJudgementStack = JudgementStack C.Raw
type AJudgementStack = JudgementStack SyntaxDesc

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

instance Eq a => Monoid (Info a) where
  mempty = Unknown
  Unknown `mappend` y = y
  x `mappend` Unknown = x
  Known x `mappend` Known y | x == y = Known x
  _ `mappend` _ = Inconsistent

instance Eq a => Semigroup (Info a) where
  (<>) = mappend

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
    Inconsistent -> throwError (IncompatibleSyntaxDescs desc desc')
    d -> pure $ case (desc, desc') of
      (Known (CdB (A _) _), _) -> desc
      (_, Known (CdB (A _) _)) -> desc'
      _ -> Syntax.contract <$> d

type ObjVar = (String, Info SyntaxDesc)
type ObjVars = Bwd ObjVar

data Kind
  = ActVar (Info SyntaxDesc) ObjVars
  | AChannel ObjVars
  | AJudgement (Maybe AJudgementStack) AProtocol
  deriving (Show)

type Hints = Map String (Info SyntaxDesc)

data Context = Context
  { objVars      :: ObjVars
  , declarations :: Decls
  , location     :: Bwd Turn
  , binderHints  :: Hints
  , currentActor :: (A.JudgementForm, Maybe AJudgementStack)
  } deriving (Show)

setCurrentActor :: A.JudgementForm -> Maybe AJudgementStack -> Context -> Context
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

resolve :: Variable -> Elab (Maybe (Either Kind (Info SyntaxDesc, DB)))
resolve (Variable x) = do
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
  | UnfinishedProtocol Channel AProtocol
  | InconsistentCommunication
  | DoomedBranchCommunicated C.Actor
  -- judgement stacks
  | PushingOnAStacklessJudgement A.JudgementForm
  | LookupFromAStacklessActor A.JudgementForm
  -- syntaxes
  | NotAValidSyntaxCat SyntaxCat
  | AlreadyDeclaredSyntaxCat SyntaxCat
  | SyntaxContainsMeta SyntaxCat
  | InvalidSyntax SyntaxCat
  -- syntaxdesc validation
  | InconsistentSyntaxDesc
  | InvalidSyntaxDesc SyntaxDesc
  | IncompatibleSyntaxDescs (Info SyntaxDesc) (Info SyntaxDesc)
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
  | ProtocolElaboration CProtocol Complaint
  deriving (Show)

data ElabState = ElabState
  { channelStates :: Map Channel ([Turn], AProtocol)
  , syntaxCats    :: Map SyntaxCat SyntaxDesc
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
        Nothing -> throwError (MetaScopeTooBig x sc ovs)
      _ -> throwError (NotAValidTermVariable x k)
    Just (Right (desc, i)) -> pure (desc, var i (length ovs))
    Nothing -> throwError (OutOfScope x)

getName :: Elab [Turn]
getName = do
  loc <- asks location
  pure (loc <>> [])

spop :: Elab (ObjVars, (Variable, Info SyntaxDesc))
spop = do
  ovs <- asks objVars
  case ovs of
    B0 -> throwError EmptyContext
    (xz :< (x, cat)) -> pure (xz, (Variable x, cat))

ssyntaxdecl :: [SyntaxCat] -> C.Raw -> Elab SyntaxDesc
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

stms :: [SyntaxDesc] -> Raw -> Elab ACTm
stms [] (At "") = atom "" <$> asks (length . objVars)
stms [] (At a) = throwError (ExpectedNilGot a)
stms [] t = throwError (ExpectedANilGot t)
stms (d:ds) (Cons p q) = (%) <$> stm d p <*> stms ds q
stms _ t = throwError (ExpectedAConsGot t)

stm :: SyntaxDesc -> Raw -> Elab ACTm
stm desc (Var v) = during (TermVariableElaboration v) $ do
  table <- gets syntaxCats
  (desc', t) <- svar v
  compatibleInfos (Known desc) desc'
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
          VNilOrCons{} -> unless (a == "") $ throwError (ExpectedNilGot a)
          VEnumOrTag es _ -> unless (a `elem` es) $ throwError (ExpectedEnumGot es a)
          VWildcard -> pure ()
          _ -> throwError (SyntaxError desc rt)
        atom a <$> asks (length . objVars)
      Cons p q -> case vdesc of
        VNilOrCons d1 d2 -> (%) <$> stm d1 p <*> stm d2 q
        VCons d1 d2 -> (%) <$> stm d1 p <*> stm d2 q
        VWildcard -> (%) <$> stm desc p <*> stm desc q
        VEnumOrTag _ ds -> case p of
          At a -> case lookup a ds of
            Nothing -> throwError (ExpectedTagGot (fst <$> ds) a)
            Just descs -> (%) <$> stm (atom "Atom" 0) p <*> stms descs q
          _ -> throwError (SyntaxError desc rt)
        _ -> throwError (SyntaxError desc rt)
      Lam (Scope (Hide x) sc) -> (x \\) <$> do
        (s, desc) <- case vdesc of
          VWildcard -> pure (Unknown, desc)
          VBind cat desc -> pure (Known (catToDesc cat), desc)
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
spat desc (C.VarP v) = during (PatternVariableElaboration v) $ do
  table <- gets syntaxCats
  ds <- asks declarations
  hs <- asks binderHints
  res <- resolve v
  case res of
    Just (Left k)  -> throwError (NotAValidPatternVariable v k)
    Just (Right (desc', i)) -> do
      compatibleInfos (Known desc) desc'
      pure (VP i, ds, hs)
    Nothing -> do
      ovs <- asks objVars
      v <- pure (getVariable v)
      pure (MP v (ones (length ovs)), ds :< (v, ActVar (Known desc) ovs), hs)
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
          VNilOrCons{} -> unless (a == "") $ throwError (ExpectedNilGot a)
          VEnumOrTag es _ -> unless (a `elem` es) $ throwError (ExpectedEnumGot es a)
          VWildcard -> pure ()
          _ -> throwError (SyntaxPError desc rp)
        (AP a,,) <$> asks declarations <*> asks binderHints

      ConsP p q -> case vdesc of
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
          AtP a -> case lookup a ds of
            Nothing -> throwError (ExpectedTagGot (fst <$> ds) a)
            Just descs ->  do
              (p, ds, hs) <- spat (atom "Atom" 0) p
              (q, ds, hs) <- local (setDecls ds . setHints hs) (spats descs q)
              pure (PP p q, ds, hs)
          _ -> throwError (SyntaxPError desc rp)
        _ -> throwError (SyntaxPError desc rp)

      LamP (Scope v@(Hide x) p) -> do
        (s, desc) <- case vdesc of
          VWildcard -> pure (Unknown, desc)
          VBind cat desc -> pure (Known (catToDesc cat), desc)
          _ -> throwError (SyntaxPError desc rp)

        () <$ isFresh (Variable x)
        (p, ds, hs) <- local (declareObjVar (x, s) . addHint x s) $ spat desc p
        pure (BP v p, ds, hs)

isChannel :: Variable -> Elab Channel
isChannel ch = resolve ch >>= \case
  Just (Left (AChannel sc)) -> pure (Channel $ getVariable ch)
  Just mk -> throwError (NotAValidChannel ch $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope ch)

isJudgement :: Variable -> Elab (A.JudgementForm, Maybe AJudgementStack, AProtocol)
isJudgement jd = resolve jd >>= \case
  Just (Left (AJudgement mstk p)) -> pure (getVariable jd, mstk, p)
  Just mk -> throwError (NotAValidJudgement jd $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope jd)

channelScope :: Channel -> Elab ObjVars
channelScope (Channel ch) = do
  ds <- asks declarations
  case fromJust (focusBy (\ (y, k) -> k <$ guard (ch == y)) ds) of
    (_, AChannel sc, _) -> pure sc

steppingChannel :: Channel -> (AProtocol -> Elab (SyntaxDesc, AProtocol)) ->
                   Elab SyntaxDesc
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
  a <- local (declare rch (AChannel ovs)) $ ma
  close ch
  pure a

guessDesc :: Raw -> Elab (Info SyntaxDesc)
guessDesc (Var v) = resolve v >>= \case
  Just (Right (info, i)) -> pure info
  Just (Left (ActVar info _)) -> pure info
  _ -> pure Unknown
guessDesc _ = pure Unknown

sact :: C.Actor -> Elab A.Actor
sact = \case
  C.Win -> pure A.Win
  C.Constrain s t -> do
    infoS <- guessDesc s
    infoT <- guessDesc t
    desc <- during (ConstrainSyntaxCatGuess s t) $
      fromInfo =<< compatibleInfos infoS infoT
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
    desc <- steppingChannel ch $ \case
      (Output, desc) : p -> pure (desc, p)
      _ -> throwError (InvalidSend ch)

    -- Send
    tm <- during (SendTermElaboration ch tm) $ do
      sc <- channelScope ch
      ovs <- asks objVars
      let (thx, xyz, thy) = lintersection sc ovs
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

  C.FreshMeta desc (av, a) -> during FreshMetaElaboration $ do
    syndecls <- gets (Map.keys . syntaxCats)
    desc <- ssyntaxdecl syndecls desc
    av <- isFresh av
    ovs <- asks objVars
    a <- local (declare av (ActVar (Known desc) ovs)) $ sact a
    pure $ A.FreshMeta desc (ActorMeta av, a)

  C.Under (Scope v@(Hide x) a) -> do
    during UnderElaboration $ () <$ isFresh (Variable x)
    a <- local (declareObjVar (x, Unknown)) $ sact a
    pure $ A.Under (Scope v a)

  C.Match rtm@tm cls -> do
    desc <- fromInfo =<< guessDesc rtm
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
      Just (Right (cat, i)) -> i <$ compatibleInfos cat (Known $ keyDesc stk)
      Just (Left k) -> throwError $ NotAValidPatternVariable p k
      _ -> throwError $ OutOfScope p
    t <- during (PushTermElaboration t) $ stm (valueDesc stk) t
    a <- sact a
    pure $ A.Push jd (p, t) a

  C.Lookup rt@t (av, a) b -> do
    (jd, stk) <- asks currentActor >>= \case
      (jd, Nothing) -> throwError (LookupFromAStacklessActor jd)
      (jd, Just stk) -> pure (jd, stk)
    t <- during (LookupTermElaboration t) $ stm (keyDesc stk) t
    av <- isFresh av
    ovs <- asks objVars
    (a, mcha) <- local (declare av (ActVar (Known $ valueDesc stk) ovs)) $ sbranch a
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
