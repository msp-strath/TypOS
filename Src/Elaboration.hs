{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses #-}

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

import Concrete.Base (Variable, Raw(..), SbstC(..), RawP(..), ThDirective(..))
import qualified Concrete.Base as C

import Term.Base
import Term.Substitution
import Pattern as P
import Actor (ActorMeta(..), Channel(..), PatActor(..), MatchLabel(..))
import qualified Actor as A

data Mode = Input | {- Subject | -} Output
  deriving (Show, Eq)

type ObjVars = Bwd String
type Protocol = [(Mode, SyntaxCat)]

data Kind
  = ActVar ObjVars
  | AChannel ObjVars Protocol
  | AJudgement Protocol
  deriving (Show)

isAJudgement :: Kind -> Maybe (Protocol)
isAJudgement (AJudgement p) = pure p
isAJudgement _ = Nothing

data Context = Context
  { objVars      :: ObjVars
  , declarations :: Decls
  , location     :: Bwd Turn
  } deriving (Show)

data Turn = West | East
  deriving (Show, Eq)

declareObjVar :: String -> Context -> Context
declareObjVar x ctx = ctx { objVars = objVars ctx :< x }

setObjVars :: ObjVars -> Context -> Context
setObjVars ovs ctx = ctx { objVars = ovs }

declare :: String -> Kind -> Context -> Context
declare x k ctx = ctx { declarations = declarations ctx :< (x, k) }

turn :: Turn -> Context -> Context
turn t ds = ds { location = location ds :< t }

setDecls :: Decls -> Context -> Context
setDecls ds ctx = ctx { declarations = ds }

type Decls = Bwd (String, Kind)
type Slced = [(String, Kind)]
type Focus a = (Decls, a, Slced)

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust Nothing k = pure ()
whenJust (Just a) k = k a

resolve :: Variable -> Elab (Maybe (Either Kind Int))
resolve x = do
  ctx <- ask
  let ds  = declarations ctx
  let ovs = objVars ctx
  case focusBy (\ (y, k) -> k <$ guard (x == y)) ds of
    Just (_, k, _) -> pure (Just $ Left k)
    _ -> case focus x ovs of
      Just (xz, _, xs) -> pure (Just $ Right (length xs))
      Nothing -> pure Nothing

isFresh :: String -> Elab ()
isFresh x = do
  res <- resolve x
  whenJust res $ \ _ -> throwError (VariableShadowing x)

data Complaint
  = OutOfScope Variable
  | InvalidTermVariable Variable Kind
  | MetaScopeTooBig Variable ObjVars ObjVars
  | VariableShadowing Variable
  | EmptyContext
  | NotTopVariable Variable Variable
  | InvalidPatternVariable Variable Kind
  | NotAValidJudgement Variable
  | InvalidSend Channel
  | InvalidRecv Channel
  | NotAValidChannel Variable
  | NonLinearChannelUse Channel
  | UnfinishedProtocol Channel Protocol
  | InconsistentCommunication
  | DoomedBranchCommunicated RawP
  deriving (Show)

type ElabState = Map Channel ([Turn], Protocol)

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

type ACTm = CdB (Tm ActorMeta)
type ACTSbst = CdB (Sbst ActorMeta)

svar :: Variable -> Elab ACTm
svar x = do
  ovs <- asks objVars
  res <- resolve x
  case res of
    Just (Left k) -> case k of
      ActVar sc -> case findSub sc ovs of
        Just th -> pure (ActorMeta x $: sbstW (sbst0 0) th)
        Nothing -> throwError (MetaScopeTooBig x sc ovs)
      _ -> throwError (InvalidTermVariable x k)
    Just (Right i) -> pure $ var i (length ovs)
    Nothing -> throwError (OutOfScope x)

getName :: Elab [Turn]
getName = do
  loc <- asks location
  pure (loc <>> [])

spop :: Elab (ObjVars, String)
spop = do
  ovs <- asks objVars
  case ovs of
    B0 -> throwError EmptyContext
    (xz :< x) -> pure (xz, x)

ssbst :: Bwd SbstC -> Elab (ACTSbst, ObjVars)
ssbst B0 = do
    ovs <- asks objVars
    pure (sbstI (length ovs), ovs)
ssbst (sg :< sgc) = case sgc of
    Keep v -> do
      (xz, w) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst sg)
      pure (sbstW sg (ones 1), ovs :< w)
    Drop v -> do
      (xz, w) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst sg)
      pure (weak sg, ovs)
    Assign v t -> do
      t <- stm t
      (sg, ovs) <- ssbst sg
      local (setObjVars ovs) $ isFresh v
      pure (sbstT sg ((Hide v :=) $^ t), ovs :< v)

sth :: (Bwd Variable, ThDirective) -> Elab Th
sth (xz, b) = do
  ovs <- asks objVars
  let th = which (`elem` xz) ovs
  pure $ case b of
    ThKeep -> th
    ThDrop -> comp th

stm :: Raw -> Elab ACTm
stm = \case
  Var v -> svar v
  At a -> atom a <$> asks (length . objVars)
  Cons p q -> (%) <$> stm p <*> stm q
  Lam (Scope (Hide x) sc) -> (x \\) <$> do
    isFresh x
    local (declareObjVar x) $ stm sc
  Sbst sg t -> do
    (sg, ovs) <- ssbst sg
    t <- local (setObjVars ovs) (stm t)
    pure (t //^ sg)

spat :: RawP -> Elab (PatF PatVar, Decls)
spat = \case
  C.VarP v -> do
    ds <- asks declarations
    res <- resolve v
    case res of
      Just (Left k)  -> throwError (InvalidPatternVariable v k)
      Just (Right i) -> pure (VP (P.VarP i), ds)
      Nothing        -> do ovs <- asks objVars
                           pure (MP v (ones (length ovs)), ds :< (v, ActVar ovs))
  AtP at -> (AP at,) <$> asks declarations
  ConsP p q -> do
    (p, ds) <- spat p
    (q, ds) <- local (setDecls ds) (spat q)
    pure (PP p q, ds)
  LamP (Scope v@(Hide x) p) -> do
    isFresh x
    (p, ds) <- local (declareObjVar x) (spat p)
    pure (BP v p, ds)
  ThP th p -> do
    th <- sth th
    (p, ds) <- spat p
    pure (th ^? p, ds)

channelScope :: Channel -> Elab ObjVars
channelScope (Channel ch) = do
  ds <- asks declarations
  case fromJust (focusBy (\ (y, k) -> k <$ guard (ch == y)) ds) of
    (_, AChannel sc _, _) -> pure sc

steppingChannel :: Channel -> (Protocol -> Elab Protocol) -> Elab ()
steppingChannel ch step = do
  nm <- getName
  (pnm, p) <- gets (fromJust . Map.lookup ch)
  unless (pnm `isPrefixOf` nm) $ throwError (NonLinearChannelUse ch)
  p <- step p
  modify (Map.insert ch (nm, p))

sact :: C.Actor -> Elab A.Actor
sact = \case
  C.Win -> pure A.Win
  C.Fail err -> A.Fail err <$ tell (All False)
  C.Constrain s t -> A.Constrain <$> stm s <*> stm t

  a C.:|: b -> do
    a <- local (turn West) $ sact a
    b <- local (turn East) $ sact b
    pure (a A.:|: b)

  C.Spawn jd rch a -> do
    -- check the channel name is fresh & initialise it
    isFresh rch
    ch <- pure (Channel rch)
    nm <- getName
    p <- resolve jd >>= \case
      Just (Left (AJudgement p)) -> pure p
      _ -> throwError (NotAValidJudgement jd)
    modify (Map.insert ch (nm, p))

    -- run the actor in the extended context
    ovs <- asks objVars
    a <- local (declare rch (AChannel ovs p)) $ sact a

    -- make sure the protocol was run all the way
    mp <- gets (Map.lookup ch)
    case snd (fromJust mp) of
      [] -> pure ()
      p -> throwError (UnfinishedProtocol ch p)
    modify (Map.delete ch)

    pure $ A.Spawn jd ch a

  C.Send ch tm a -> do
    -- Check the channel is in sending mode & step it
    ch <- pure (Channel ch)
    steppingChannel ch $ \case
      (Output, cat) : p -> pure p
      _ -> throwError (InvalidSend ch)

    -- Send
    sc <- channelScope ch
    ovs <- asks objVars
    let (thx, xyz, thy) = lintersection sc ovs
    tm <- (*^ thx) <$> local (setObjVars xyz) (stm tm)

    a <- sact a
    pure $ A.Send ch tm a

  C.Recv ch av a -> do
    isFresh av
    -- Check the channel is in receiving mode & step it
    ch <- pure (Channel ch)
    steppingChannel ch $ \case
      (Input, cat) : p -> pure p
      _ -> throwError (InvalidRecv ch)

    -- Receive
    sc <- channelScope ch
    a <- local (declare av (ActVar sc)) $ sact a
    pure $ A.Recv ch (ActorMeta av) a

  C.FreshMeta av a -> do
    isFresh av
    ovs <- asks objVars
    a <- local (declare av (ActVar ovs)) $ sact a
    pure $ A.FreshMeta (ActorMeta av) a

  C.Under (Scope v@(Hide x) a) -> do
    isFresh x
    a <- local (declareObjVar x) $ sact a
    pure $ A.Under (Scope v a)

  C.Match ml tm cls -> do
    ml <- pure (MatchLabel ml)
    tm <- stm tm
    chs <- get
    clsts <- traverse sclause cls
    let (cls, sts) = unzip clsts
    case groupBy ((==) `on` fmap snd) [ p | Just p <- sts ] of
      [] -> tell (All False) -- all branches are doomed, we don't care
      [(c:_)] -> put c
      _ -> throwError InconsistentCommunication
    pure $ A.Match ml tm cls

  C.Extend (jd, ml, y, a) b -> do
    y <- resolve y >>= \case
           Just (Right i) -> pure (P.VarP i)
           _ -> throwError (OutOfScope y)
    a <- sact a -- a should communicate in a manner compatible with jd/ml
                -- protocol inference?
    b <- sact b
    pure $ A.Extend (jd, MatchLabel (Just ml), y, a) b

  C.Print fmt a -> A.Print <$> traverse (traverse stm) fmt <*> sact a
  C.Break str a -> A.Break str <$> sact a

sclause :: (RawP, C.Actor) -> Elab ((PatActor, A.Actor), Maybe ElabState)
sclause (rp, a) = do
  chs <- get
  (p, ds) <- spat rp
  (a, All b) <- local (setDecls ds) $ censor (const (All True)) $ listen $ sact a
  chs' <- get
  unless b $ unless (chs == chs') $ throwError (DoomedBranchCommunicated rp)
  put chs
  pure ((p, a), chs' <$ guard b)
