{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses #-}

module Elaboration where

import Control.Monad.Reader
import Control.Monad.Except

import Data.Monoid

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

type Context = Bwd (String, Kind)
type Txetnoc = [(String, Kind)]
type Focus a = (Context, a, Txetnoc)

objVars :: Context -> Bwd String
objVars = foldMap $ \case
  (x , ObjVar _) -> B0 :< x
  _ -> B0

countObjVars :: Foldable t => t (String, Kind) -> Int
countObjVars = getSum . foldMap (\case
  (_, ObjVar _) -> 1
  _ -> 0)

focusBy :: (String -> Kind -> Maybe a) -> Context -> Maybe (Focus a)
focusBy p ctx = go ctx [] where

  go B0 _ = Nothing
  go (xz :< x) xs
    | Just a <- uncurry p x = pure (xz, a, xs)
    | otherwise = go xz (x : xs)

focus :: String -> Context -> Maybe (Focus Kind)
focus v = focusBy (\ w k -> k <$ guard (v == w))

isFresh :: String -> Elab ()
isFresh x = do
  ctx <- ask
  whenJust (focus x ctx) $ \ _ -> throwError (VariableShadowing x)

data Complaint
  = OutOfScope Variable
  | InvalidTermVariable Variable Kind
  | MetaScopeTooBig Variable LocalOVs Context
  | VariableShadowing Variable
  | EmptyContext
  | NotTopVariable Variable Variable
  | InvalidPatternVariable Variable Kind
  | NotAValidJudgement Variable
  | InvalidSend Variable
  | InvalidRecv Variable
  | NotAValidChannel Variable
  deriving (Show)

newtype Elab a = Elab { runElab :: ReaderT Context (Either Complaint) a }
  deriving ( Functor, Applicative, Monad
           , MonadReader Context
           , MonadError Complaint)

type ACTm = CdB (Tm ActorMeta)
type ACTSbst = CdB (Sbst ActorMeta)

svar :: Variable -> Elab ACTm
svar x = do
  ctx <- ask
  case focus x ctx of
    Nothing -> throwError (OutOfScope x)
    Just (xz, k, xs) -> case k of
      ObjVar cat -> pure $ var (countObjVars xs) (countObjVars ctx)
      ActVar sc -> case findSub sc (objVars ctx) of
        Just th -> pure (ActorMeta x $: sbstW (sbst0 0) th)
        Nothing -> throwError (MetaScopeTooBig x sc ctx)
      _ -> throwError (InvalidTermVariable x k)

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust Nothing k = pure ()
whenJust (Just a) k = k a

sscope :: Kind ->
          (t -> Elab u) ->
          (Scope t -> Elab u)
sscope mk el (Scope v@(Hide x) t) = do
  isFresh x
  local (:< (x, mk)) (el t)

spop :: Elab (Focus (String, Maybe SyntaxCat))
spop = do
  ctx <- ask
  case focusBy (\ v k -> (v,) <$> isObjVar k) ctx of
    Nothing -> throwError EmptyContext
    Just foc -> pure foc

ssbst :: Bwd SbstC -> Elab (ACTSbst, Context)
ssbst B0 = do
    ctx <- ask
    pure (sbstI (countObjVars ctx), ctx)
ssbst (sg :< sgc) = case sgc of
    Keep v -> do
      (xz, (w, cat), xs) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ctx) <- local (const $ xz <>< xs) (ssbst sg)
      pure (sbstW sg (ones 1), ctx :< (w, ObjVar cat))
    Drop v -> do
      (xz, (w, cat), xs) <- spop
      when (v /= w) $ throwError (NotTopVariable v w)
      (sg, ctx) <- local (const $ xz <>< xs) (ssbst sg)
      pure (weak sg, ctx)
    Assign v t -> do
      t <- stm t
      (sg, ctx) <- ssbst sg
      local (const ctx) $ isFresh v
      pure (sbstT sg ((Hide v :=) $^ t), ctx :< (v, ObjVar Nothing))

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
  At a -> atom a . countObjVars <$> ask
  Cons p q -> (%) <$> stm p <*> stm q
  Lam sc -> (boundName sc \\) <$> sscope (ObjVar Nothing) stm sc
  Sbst sg t -> do
    (sg, ctx) <- ssbst sg
    t <- local (const ctx) (stm t)
    pure (t //^ sg)

spat :: RawP -> Elab (PatF PatVar, Context)
spat = \case
  C.VarP v -> do
    ctx <- ask
    case focus v ctx of
      Just (xz, ObjVar _, xs) -> pure (VP (P.VarP $ countObjVars xs), ctx)
      Just (xz, k, xs) -> throwError (InvalidPatternVariable v k)
      Nothing -> let xz = objVars ctx in
                 pure (MP v (ones (length xz)), ctx :< (v, ActVar xz))
  AtP at -> (AP at,) <$> ask
  ConsP p q -> do
    (p, ctx) <- spat p
    (q, ctx) <- local (const ctx) (spat q)
    pure (PP p q, ctx)
  LamP (Scope v@(Hide x) p) -> do
    isFresh x
    (p, ctx) <- local (:< (x, ObjVar Nothing)) (spat p)
    (xz, (y, _), xs) <- local (const ctx) spop
    when (x /= y) $ error "The IMPOSSIBLE happened"
    pure (BP v p, xz <>< xs)
  ThP th p -> do
    th <- sth th
    (p, ctx) <- spat p
    pure (th ^? p, ctx)

sact :: C.Actor -> Elab A.Actor
sact = \case
  a C.:|: b -> (A.:|:) <$> sact a <*> sact b
  C.Spawn jd ch a -> do
    isFresh ch
    ctx <- ask
    p <- case focus jd ctx of
      Just (_, AJudgement p, _) -> pure p
      _ -> throwError (NotAValidJudgement jd)
    xz <- asks objVars
    a <- local (:< (ch, AChannel xz p)) $ sact a
    pure $ A.Spawn jd (Channel ch) a
  C.Send ch tm a -> do
    ctx <- ask
    (sc, ctx) <- case focus ch ctx of
      Just (xz, AChannel sc ((Output, cat) : p), xs) ->
        pure (sc, (xz <>< (ch, AChannel sc p) : xs))
      Just (xz, AChannel _ _, _) -> throwError (InvalidSend ch)
      _ -> throwError (NotAValidChannel ch)
    local (const ctx) $ do
      tm <- stm tm -- this needs to fit on the ch wire
      a <- sact a
      pure $ A.Send (Channel ch) tm a
  C.Recv ch av a -> do
    isFresh av
    ctx <- ask
    (sc, ctx) <- case focus ch ctx of
      Just (xz, AChannel sc ((Input, cat) : p), xs) ->
        pure (sc, (xz <>< (ch, AChannel sc p) : xs))
      Just (xz, AChannel _ _, _) -> throwError (InvalidRecv ch)
      _ -> throwError (NotAValidChannel ch)
    local (const ctx) $ do
      a <- local (:< (av, ActVar sc)) (sact a)
      pure $ A.Recv (Channel ch) (ActorMeta av) a
