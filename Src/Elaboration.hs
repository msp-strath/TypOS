{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses #-}

module Elaboration where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.List (isPrefixOf)
import Data.Maybe
import Data.Monoid
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
import Actor (ActorMeta(..), Channel(..))
import qualified Actor as A

data Mode = Input | {- Subject | -} Output
  deriving (Show)

type LocalOVs = Bwd String
type Protocol = [(Mode, SyntaxCat)]

data Kind
  = ObjVar (Maybe SyntaxCat)
  | ActVar LocalOVs
  | AChannel LocalOVs Protocol
  | AJudgement Protocol
  deriving (Show)

isObjVar :: Kind -> Maybe (Maybe SyntaxCat)
isObjVar (ObjVar cat) = pure cat
isObjVar _ = Nothing

isAJudgement :: Kind -> Maybe (Protocol)
isAJudgement (AJudgement p) = pure p
isAJudgement _ = Nothing

data Context = Context
  { declarations :: Decls
  , location     :: Bwd Turn
  } deriving (Show)

data Turn = West | East
  deriving (Show, Eq)

declare :: String -> Kind -> Context -> Context
declare x k ctx = ctx { declarations = declarations ctx :< (x, k) }

turn :: Turn -> Context -> Context
turn t ds = ds { location = location ds :< t }

setDecls :: Decls -> Context -> Context
setDecls ds ctx = ctx { declarations = ds }

type Decls = Bwd (String, Kind)
type Slced = [(String, Kind)]
type Focus a = (Decls, a, Slced)

objVars :: Decls -> Bwd String
objVars = foldMap $ \case
  (x , ObjVar _) -> B0 :< x
  _ -> B0

countObjVars :: Foldable t => t (String, Kind) -> Int
countObjVars = getSum . foldMap (\case
  (_, ObjVar _) -> 1
  _ -> 0)

focusBy :: (String -> Kind -> Maybe a) -> Decls -> Maybe (Focus a)
focusBy p ds = go ds [] where

  go B0 _ = Nothing
  go (xz :< x) xs
    | Just a <- uncurry p x = pure (xz, a, xs)
    | otherwise = go xz (x : xs)

focus :: String -> Decls -> Maybe (Focus Kind)
focus v = focusBy (\ w k -> k <$ guard (v == w))

isFresh :: String -> Elab ()
isFresh x = do
  ds <- asks declarations
  whenJust (focus x ds) $ \ _ -> throwError (VariableShadowing x)

data Complaint
  = OutOfScope Variable
  | InvalidTermVariable Variable Kind
  | MetaScopeTooBig Variable LocalOVs Decls
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
  deriving (Show)

type ElabState = Map Channel ([Turn], Protocol)

newtype Elab a = Elab
  { runElab :: StateT ElabState
               (ReaderT Context
               (Either Complaint))
               a }
  deriving ( Functor, Applicative, Monad
           , MonadReader Context
           , MonadState ElabState
           , MonadError Complaint)

type ACTm = CdB (Tm ActorMeta)
type ACTSbst = CdB (Sbst ActorMeta)

svar :: Variable -> Elab ACTm
svar x = do
  ds <- asks declarations
  case focus x ds of
    Nothing -> throwError (OutOfScope x)
    Just (xz, k, xs) -> case k of
      ObjVar cat -> pure $ var (countObjVars xs) (countObjVars ds)
      ActVar sc -> case findSub sc (objVars ds) of
        Just th -> pure (ActorMeta x $: sbstW (sbst0 0) th)
        Nothing -> throwError (MetaScopeTooBig x sc ds)
      _ -> throwError (InvalidTermVariable x k)

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust Nothing k = pure ()
whenJust (Just a) k = k a

getName :: Elab [Turn]
getName = do
  loc <- asks location
  pure (loc <>> [])

sscope :: Kind ->
          (t -> Elab u) ->
          (Scope t -> Elab u)
sscope mk el (Scope v@(Hide x) t) = do
  isFresh x
  local (declare x mk) (el t)

spop :: Elab (Focus (String, Maybe SyntaxCat))
spop = do
  ds <- asks declarations
  case focusBy (\ v k -> (v,) <$> isObjVar k) ds of
    Nothing -> throwError EmptyContext
    Just foc -> pure foc

ssbst :: Bwd SbstC -> Elab (ACTSbst, Decls)
ssbst B0 = do
    ds <- asks declarations
    pure (sbstI (countObjVars ds), ds)
ssbst (sg :< sgc) = case sgc of
    Keep v -> do
      (xz, (w, cat), xs) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ctx) <- local (setDecls $ xz <>< xs) (ssbst sg)
      pure (sbstW sg (ones 1), ctx :< (w, ObjVar cat))
    Drop v -> do
      (xz, (w, cat), xs) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ctx) <- local (setDecls $ xz <>< xs) (ssbst sg)
      pure (weak sg, ctx)
    Assign v t -> do
      t <- stm t
      (sg, ds) <- ssbst sg
      local (setDecls ds) $ isFresh v
      pure (sbstT sg ((Hide v :=) $^ t), ds :< (v, ObjVar Nothing))

sth :: (Bwd Variable, ThDirective) -> Elab Th
sth (xz, b) = do
  ovs <- asks (objVars . declarations)
  let th = which (`elem` xz) ovs
  pure $ case b of
    ThKeep -> th
    ThDrop -> comp th

stm :: Raw -> Elab ACTm
stm = \case
  Var v -> svar v
  At a -> atom a . countObjVars <$> asks declarations
  Cons p q -> (%) <$> stm p <*> stm q
  Lam sc -> (boundName sc \\) <$> sscope (ObjVar Nothing) stm sc
  Sbst sg t -> do
    (sg, ctx) <- ssbst sg
    t <- local (setDecls ctx) (stm t)
    pure (t //^ sg)

spat :: RawP -> Elab (PatF PatVar, Decls)
spat = \case
  C.VarP v -> do
    ds <- asks declarations
    case focus v ds of
      Just (xz, ObjVar _, xs) -> pure (VP (P.VarP $ countObjVars xs), ds)
      Just (xz, k, xs) -> throwError (InvalidPatternVariable v k)
      Nothing -> let xz = objVars ds in
                 pure (MP v (ones (length xz)), ds :< (v, ActVar xz))
  AtP at -> (AP at,) <$> asks declarations
  ConsP p q -> do
    (p, ds) <- spat p
    (q, ds) <- local (setDecls ds) (spat q)
    pure (PP p q, ds)
  LamP (Scope v@(Hide x) p) -> do
    isFresh x
    (p, ds) <- local (declare x $ ObjVar Nothing) (spat p)
    (xz, (y, _), xs) <- local (setDecls ds) spop
    when (x /= y) $ error "The IMPOSSIBLE happened"
    pure (BP v p, xz <>< xs)
  ThP th p -> do
    th <- sth th
    (p, ds) <- spat p
    pure (th ^? p, ds)

channelScope :: Channel -> Elab LocalOVs
channelScope (Channel ch) = do
  ds <- asks declarations
  case fromJust (focus ch ds) of
    (xz, AChannel sc _, xs) -> pure sc

steppingChannel :: Channel -> (Protocol -> Elab Protocol) -> Elab ()
steppingChannel ch step = do
  nm <- getName
  (pnm, p) <- gets (fromJust . Map.lookup ch)
  unless (pnm `isPrefixOf` nm) $ throwError (NonLinearChannelUse ch)
  p <- step p
  modify (Map.insert ch (nm, p))

sact :: C.Actor -> Elab A.Actor
sact = \case
  a C.:|: b -> do
    a <- local (turn West) $ sact a
    b <- local (turn East) $ sact b
    pure (a A.:|: b)
  C.Spawn jd rch a -> do
    -- check the channel name is fresh & initialise it
    isFresh rch
    ch <- pure (Channel rch)
    nm <- getName
    ds <- asks declarations
    p <- case focus jd ds of
      Just (_, AJudgement p, _) -> pure p
      _ -> throwError (NotAValidJudgement jd)
    modify (Map.insert ch (nm, p))

    -- run the actor in the extended context
    xz <- asks (objVars . declarations)
    a <- local (declare rch (AChannel xz p)) $ sact a

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
    tm <- stm tm -- this needs to fit on the ch wire
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
    ovs <- asks (objVars . declarations)
    a <- local (declare av (ActVar ovs)) $ sact a
    pure $ A.FreshMeta (ActorMeta av) a
