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

dual :: Protocol -> Protocol
dual = map $ \case
  (Input, c) -> (Output, c)
  (Output, c) -> (Input, c)

type ObjVars = Bwd String

data Kind
  = ActVar ObjVars
  | AChannel ObjVars
  | AJudgement Protocol
  deriving (Show)

data Context = Context
  { objVars      :: ObjVars
  , declarations :: Decls
  , location     :: Bwd Turn
  } deriving (Show)

initContext :: Context
initContext = Context B0 B0 B0

data Turn = West | East
  deriving (Show, Eq)

declareObjVar :: String -> Context -> Context
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

type Decls = Bwd (String, Kind)
type Slced = [(String, Kind)]
type Focus a = (Decls, a, Slced)

resolve :: Variable -> Elab (Maybe (Either Kind DB))
resolve (Variable x) = do
  ctx <- ask
  let ds  = declarations ctx
  let ovs = objVars ctx
  case focusBy (\ (y, k) -> k <$ guard (x == y)) ds of
    Just (_, k, _) -> pure (Just $ Left k)
    _ -> case focus x ovs of
      Just (xz, _, xs) -> pure (Just $ Right (DB $ length xs))
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
  -- syntaxes
  | NotAValidSyntaxCat SyntaxCat
  | AlreadyDeclaredSyntaxCat SyntaxCat
  | SyntaxContainsMeta SyntaxCat
  | InvalidSyntax SyntaxCat
  -- contextual info
  | SendTermElaboration Channel Raw Complaint
  | MatchTermElaboration Raw Complaint
  | MatchElaboration Raw Complaint
  | MatchBranchElaboration RawP Complaint
  | ConstrainTermElaboration Raw Complaint
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
  deriving (Show)

data ElabState = ElabState
  { channelStates :: Map Channel ([Turn], Protocol)
  , syntaxCats    :: Map SyntaxCat SyntaxDesc
  } deriving (Eq)

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

svar :: Variable -> Elab ACTm
svar x = do
  ovs <- asks objVars
  res <- resolve x
  case res of
    Just (Left k) -> case k of
      ActVar sc -> case findSub sc ovs of
        Just th -> pure (ActorMeta (getVariable x) $: sbstW (sbst0 0) th)
        Nothing -> throwError (MetaScopeTooBig x sc ovs)
      _ -> throwError (NotAValidTermVariable x k)
    Just (Right i) -> pure $ var i (length ovs)
    Nothing -> throwError (OutOfScope x)

getName :: Elab [Turn]
getName = do
  loc <- asks location
  pure (loc <>> [])

spop :: Elab (ObjVars, Variable)
spop = do
  ovs <- asks objVars
  case ovs of
    B0 -> throwError EmptyContext
    (xz :< x) -> pure (xz, Variable x)

ssbst :: Bwd SbstC -> Elab (ACTSbst, ObjVars)
ssbst B0 = do
    ovs <- asks objVars
    pure (sbstI (length ovs), ovs)
ssbst (sg :< sgc) = case sgc of
    Keep v -> do
      (xz, w) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst sg)
      pure (sbstW sg (ones 1), ovs :< getVariable w)
    Drop v -> do
      (xz, w) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst sg)
      pure (weak sg, ovs)
    Assign v t -> do
      t <- stm t
      (sg, ovs) <- ssbst sg
      v <- local (setObjVars ovs) $ isFresh v
      pure (sbstT sg ((Hide v :=) $^ t), ovs :< v)

sth :: (Bwd Variable, ThDirective) -> Elab Th
sth (xz, b) = do
  ovs <- asks objVars
  let th = which (`elem` (getVariable <$> xz)) ovs
  pure $ case b of
    ThKeep -> th
    ThDrop -> comp th

stm :: Raw -> Elab ACTm
stm = \case
  Var v -> svar v
  At a -> atom a <$> asks (length . objVars)
  Cons p q -> (%) <$> stm p <*> stm q
  Lam (Scope (Hide x) sc) -> (x \\) <$> do
    x <- isFresh (Variable x)
    local (declareObjVar x) $ stm sc
  Sbst sg t -> do
    (sg, ovs) <- during (SubstitutionElaboration sg) $ ssbst sg
    t <- local (setObjVars ovs) (stm t)
    pure (t //^ sg)

spat :: RawP -> Elab (Pat, Decls)
spat = \case
  C.VarP v -> do
    ds <- asks declarations
    res <- resolve v
    case res of
      Just (Left k)  -> throwError (NotAValidPatternVariable v k)
      Just (Right i) -> pure (VP i, ds)
      Nothing        -> do ovs <- asks objVars
                           v <- pure (getVariable v)
                           pure (MP v (ones (length ovs)), ds :< (v, ActVar ovs))
  AtP at -> (AP at,) <$> asks declarations
  ConsP p q -> do
    (p, ds) <- spat p
    (q, ds) <- local (setDecls ds) (spat q)
    pure (PP p q, ds)
  LamP (Scope v@(Hide x) p) -> do
    () <$ isFresh (Variable x)
    (p, ds) <- local (declareObjVar x) (spat p)
    pure (BP v p, ds)
  ThP th p -> do
    th <- sth th
    (p, ds) <- local (th ^?) $ spat p
    pure (p *^ th, ds)
  UnderscoreP -> (HP,) <$> asks declarations

isChannel :: Variable -> Elab Channel
isChannel ch = resolve ch >>= \case
  Just (Left (AChannel sc)) -> pure (Channel $ getVariable ch)
  Just mk -> throwError (NotAValidChannel ch $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope ch)

isJudgement :: Variable -> Elab (A.JudgementForm, Protocol)
isJudgement jd = resolve jd >>= \case
  Just (Left (AJudgement p)) -> pure (getVariable jd, p)
  Just mk -> throwError (NotAValidJudgement jd $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope jd)

channelScope :: Channel -> Elab ObjVars
channelScope (Channel ch) = do
  ds <- asks declarations
  case fromJust (focusBy (\ (y, k) -> k <$ guard (ch == y)) ds) of
    (_, AChannel sc, _) -> pure sc

steppingChannel :: Channel -> (Protocol -> Elab Protocol) -> Elab ()
steppingChannel ch step = do
  nm <- getName
  (pnm, p) <- gets (fromJust . channelLookup ch)
  unless (pnm `isPrefixOf` nm) $ throwError (NonLinearChannelUse ch)
  p <- step p
  modify (channelInsert ch (nm, p))

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

sact :: C.Actor -> Elab A.Actor
sact = \case
  C.Win -> pure A.Win
  C.Constrain s t -> do
    s <- during (ConstrainTermElaboration s) $ stm s
    t <- during (ConstrainTermElaboration t) $ stm t
    pure $ A.Constrain s t

  a C.:|: b -> do
    a <- local (turn West) $ sact a
    b <- local (turn East) $ sact b
    pure (a A.:|: b)

  C.Spawn jd ch a -> do
    -- check the channel name is fresh & initialise it
    ch <- Channel <$> isFresh ch
    (jd, p) <- isJudgement jd

    a <- withChannel ch (dual p) $ sact a

    pure $ A.Spawn jd ch a

  C.Send ch tm a -> do
    ch <- isChannel ch
    -- Check the channel is in sending mode, & step it
    steppingChannel ch $ \case
      (Output, cat) : p -> pure p
      _ -> throwError (InvalidSend ch)

    -- Send
    tm <- during (SendTermElaboration ch tm) $ do
      sc <- channelScope ch
      ovs <- asks objVars
      let (thx, xyz, thy) = lintersection sc ovs
      (*^ thx) <$> local (setObjVars xyz) (stm tm)

    a <- sact a
    pure $ A.Send ch tm a

  C.Recv ch (av, a) -> do
    ch <- isChannel ch
    av <- during (RecvMetaElaboration ch) $ isFresh av
    -- Check the channel is in receiving mode & step it
    steppingChannel ch $ \case
      (Input, cat) : p -> pure p
      _ -> throwError (InvalidRecv ch)

    -- Receive
    sc <- channelScope ch
    a <- local (declare av (ActVar sc)) $ sact a
    pure $ A.Recv ch (ActorMeta av, a)

  C.FreshMeta (av, a) -> do
    av <- during FreshMetaElaboration $ isFresh av
    ovs <- asks objVars
    a <- local (declare av (ActVar ovs)) $ sact a
    pure $ A.FreshMeta (ActorMeta av, a)

  C.Under (Scope v@(Hide x) a) -> do
    during UnderElaboration $ () <$ isFresh (Variable x)
    a <- local (declareObjVar x) $ sact a
    pure $ A.Under (Scope v a)

  C.Match rtm@tm cls -> do
    tm <- during (MatchTermElaboration tm) $ stm tm
    chs <- get
    clsts <- traverse sclause cls
    let (cls, sts) = unzip clsts
    during (MatchElaboration rtm) $ consistentCommunication sts
    pure $ A.Match tm cls

  C.Push jd (p, t) a -> do
    (jd, _) <- isJudgement jd

    p <- resolve p >>= \case
      Just (Right i) -> pure i
      Just (Left k) -> throwError $ NotAValidPatternVariable p k
      _ -> throwError $ OutOfScope p
    t <- during (PushTermElaboration t) $ stm t
    a <- sact a
    pure $ A.Push jd (p, t) a

  C.Lookup rt@t (av, a) b -> do
    t <- during (LookupTermElaboration t) $ stm t
    av <- isFresh av
    ovs <- asks objVars
    (a, mcha) <- local (declare av (ActVar ovs)) $ sbranch a
    (b, mchb) <- sbranch b
    during (LookupHandlersElaboration rt) $ consistentCommunication [mcha, mchb]
    pure $ A.Lookup t (ActorMeta av, a) b

  C.Fail fmt -> A.Fail <$> traverse (traverse stm) fmt <* tell (All False)
  C.Print fmt a -> A.Print <$> traverse (traverse stm) fmt <*> sact a
  C.Break fmt a -> A.Break <$> traverse (traverse stm) fmt <*> sact a

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

sclause :: (RawP, C.Actor) -> Elab ((Pat, A.Actor), Maybe ElabState)
sclause (rp, a) = during (MatchBranchElaboration rp) $ do
  (p, ds) <- spat rp
  (a, me) <- local (setDecls ds) $ sbranch a
  pure ((p, a), me)
