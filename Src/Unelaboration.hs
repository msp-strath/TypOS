{-# LANGUAGE ConstraintKinds, UndecidableInstances #-}

module Unelaboration where

import Control.Monad.Except
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map

import GHC.Stack

import Actor (ActorMeta(..), Channel(..))
import qualified Actor as A
import Bwd
import Concrete.Base
import qualified Concrete.Base as C
import Forget
import Format
import Hide
import Pattern
import Scope
import Term.Base
import Thin

type Naming =
  ( Bwd String  -- what's in the support
  , Th          -- and how that was chosen from
  , Bwd String  -- what's in scope
  )

initNaming :: Naming
initNaming = (B0, ones 0, B0)

nameOn :: Naming -> String -> Naming
nameOn (xz, th, yz) x = (xz :< x, th -? True, yz :< x)

nameSel :: Th -> Naming -> Naming
nameSel th (xz, ph, yz) = (th ?< xz, th <^> ph, yz)

freshen :: String -> Naming -> String
freshen x (xz, _, _) = head [y | y <- ys, all (y /=) xz] where
  ys = x : [x ++ show (i :: Integer) | i <- [0..]]

data Complaint = UnexpectedEmptyThinning Naming
               | VarOutOfScope Naming
               | InvalidNaming Naming
               | UnknownChannel String
  deriving (Show)

newtype UnelabM e a = Unelab
  { runUnelab :: (ReaderT e
                  (Either Complaint))
                  a }
  deriving ( Functor, Applicative, Monad
           , MonadError Complaint
           , MonadReader e)

withForget :: Forget e e' => UnelabM e' a -> UnelabM e a
withForget (Unelab md) = Unelab (withReaderT forget md)

class Unelab t where
  type UnelabEnv t
  type Unelabed t

  unelab :: HasCallStack => t -> UnelabM (UnelabEnv t) (Unelabed t)

-- type Unelab0 m = (Unelab m, UnelabEnv m ~ ())


subunelab :: (Unelab t, Forget e (UnelabEnv t)) => t -> UnelabM e (Unelabed t)
subunelab = withForget . unelab

type UnelabMeta m = (Unelab m, Forget Naming (UnelabEnv m), Unelabed m ~ Variable)

instance UnelabMeta m => Unelab (CdB (Tm m)) where
  type UnelabEnv (CdB (Tm m)) = Naming
  type Unelabed (CdB (Tm m)) = Raw
  unelab  (CdB t' th) = local (nameSel th) $ unelab t'

instance Unelab DB where
  type UnelabEnv DB = Naming
  type Unelabed DB = Variable
  unelab (DB n) = do
    na@(ns, _, _) <- ask
    when (n >= length ns) $ throwError (InvalidNaming na)
    pure (ns <! n)

instance UnelabMeta m => Unelab (Tm m) where
  type UnelabEnv (Tm m) = Naming
  type Unelabed (Tm m) = Raw
  unelab = \case
    V -> ask >>= \case
           (B0 :< x, _, _) -> pure (Var x)
           na              -> throwError (VarOutOfScope na)
    A a -> pure (At a)
    P (s :<>: t) -> Cons <$> unelab s <*> unelab t
    (x := b) :. t -> Lam . Scope x <$> case b of
            False -> unelab t
            True -> do
              na <- ask
              let y = freshen (unhide x) na
              local (`nameOn` y) $ unelab t
    m :$ sg -> Sbst <$> unelab sg <*> (Var <$> subunelab m)

instance UnelabMeta m => Unelab (Sbst m) where
  type UnelabEnv (Sbst m) = Naming
  type Unelabed (Sbst m) = Bwd SbstC
  unelab sg = do
    na@(_, th, _) <- ask
    case sg of
      (S0 :^^ _) | th == ones (bigEnd th) -> pure B0
      (ST (CdB sg th :<>: CdB (Hide x := t) ph) :^^ 0) -> do
        t <- unelab (CdB t ph)
        sg <- local (nameSel th) $ unelab sg
        pure (sg :< Assign x t)
      (sg :^^ w) -> case na of
        (_, th, _) | bigEnd th <= 0 -> throwError (UnexpectedEmptyThinning na)
        (xz, th, yz :< y) -> case thun th of
         (th, False) -> do
           sg <- local (const (xz, th, yz)) $ unelab (sg :^^ w)
           pure (sg :< Drop y)
         (th, True) ->
           case xz of
             xz :< x -> do
               sg <- local (const (xz, th, yz)) $ unelab (sg :^^ (w - 1))
               pure (sg :< Keep x)
             _ -> throwError $ InvalidNaming na
        _ -> throwError $ InvalidNaming na

instance Unelab Pat where
  type UnelabEnv Pat = Naming
  type Unelabed Pat = RawP
  unelab = \case
    VP n -> VarP <$> unelab n
    AP str -> pure (AtP str)
    PP p q -> ConsP <$> unelab p <*> unelab q
    BP x p -> LamP . Scope x <$> local (`nameOn` unhide x) (unelab p)
    MP m th -> {- TODO: insert ThP -} pure (VarP m)
    HP -> pure UnderscoreP

instance Unelab (Pat, A.Actor) where
  type UnelabEnv (Pat, A.Actor) = DAEnv
  type Unelabed  (Pat, A.Actor) = (RawP, C.Actor)
  unelab (p, a) = (,) <$> subunelab p <*> unelab a

data DAEnv = DAEnv
  { daActorNaming :: Naming
  , daChannelNaming :: Map Channel Naming
  }

initDAEnv :: DAEnv
initDAEnv = DAEnv initNaming Map.empty

declareChannel :: Channel -> DAEnv -> DAEnv
declareChannel ch rh@DAEnv{..} =
  let update = Map.insert ch daActorNaming in
  rh { daChannelNaming = update daChannelNaming }

updateNaming :: (Naming -> Naming) -> DAEnv -> DAEnv
updateNaming f rh@DAEnv{..} = rh { daActorNaming = f daActorNaming }

setNaming :: Naming -> DAEnv -> DAEnv
setNaming = updateNaming . const

inChannel :: Channel -> UnelabM DAEnv a -> UnelabM DAEnv a
inChannel ch ma = do
  asks (Map.lookup ch . daChannelNaming) >>= \case
    Nothing -> throwError $ UnknownChannel (rawChannel ch)
    Just na -> local (setNaming na) $ ma

instance Forget DAEnv Naming where
  forget = daActorNaming

instance Unelab ActorMeta where
  type UnelabEnv ActorMeta = ()
  type Unelabed ActorMeta = Variable
  unelab (ActorMeta str) = pure str

instance Unelab Channel where
  type UnelabEnv Channel = ()
  type Unelabed Channel = Variable
  unelab (Channel str)  = pure str

instance Unelab A.JudgementForm where
  type UnelabEnv A.JudgementForm = ()
  type Unelabed A.JudgementForm = Variable
  unelab str  = pure str

instance Unelab Debug where
  type UnelabEnv Debug = ()
  type Unelabed Debug = Debug
  unelab = pure

instance Unelab Directive where
  type UnelabEnv Directive = ()
  type Unelabed Directive = Directive
  unelab = pure

instance Unelab t => Unelab (Format Directive Debug t) where
  type UnelabEnv (Format Directive Debug t) = UnelabEnv t
  type Unelabed (Format Directive Debug t) = Format Directive Debug (Unelabed t)
  unelab = \case
    TermPart d t -> TermPart d <$> unelab t
    DebugPart dbg -> pure (DebugPart dbg)
    StringPart str -> pure (StringPart str)

instance Unelab A.Actor where
  type UnelabEnv A.Actor = DAEnv
  type Unelabed A.Actor = C.Actor
  unelab = \case
    a A.:|: b -> (C.:|:) <$> unelab a <*> unelab b
    A.Spawn jd ch a -> C.Spawn <$> subunelab jd <*> subunelab ch <*> unelab a
    A.Send ch tm a -> C.Send <$> subunelab ch <*> (inChannel ch $ subunelab tm) <*> unelab a
    A.Recv ch (av, a) -> C.Recv <$> subunelab ch <*> ((,) <$> subunelab av <*> unelab a)
    A.FreshMeta (av, a) -> C.FreshMeta <$> ((,) <$> subunelab av <*> unelab a)
    A.Under (Scope x a) -> C.Under . Scope x <$> local (updateNaming (`nameOn` unhide x)) (unelab a)
    A.Push jd (p, t) a -> C.Push <$> subunelab jd <*> ((,) <$> subunelab p <*> subunelab t) <*> unelab a
    A.Lookup t (av, a) b -> C.Lookup <$> subunelab t <*> ((,) <$> subunelab av <*> unelab a) <*> unelab b
    A.Match tm pts -> C.Match <$> subunelab tm <*> traverse unelab pts
    A.Constrain s t -> C.Constrain <$> subunelab s <*> subunelab t
    A.Win -> pure C.Win
    A.Fail fmt -> C.Fail <$> traverse subunelab fmt
    A.Print fmt a -> C.Print <$> traverse subunelab fmt <*> unelab a
    A.Break fmt a -> C.Break <$> traverse subunelab fmt <*> unelab a