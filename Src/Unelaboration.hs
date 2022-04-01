{-# LANGUAGE ConstraintKinds #-}

module Unelaboration where

import Control.Monad.Except
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Void

import GHC.Stack

import Actor
import Bwd
import Concrete.Base
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

withEnv :: e' -> UnelabM e' a -> UnelabM e a
withEnv rh (Unelab md) = Unelab (withReaderT (const rh) md)

evalUnelab :: e -> UnelabM e a -> Either Complaint a
evalUnelab e (Unelab m) = runReaderT m e

unsafeEvalUnelab :: e -> UnelabM e a -> a
unsafeEvalUnelab e m = either (error . show) id $ evalUnelab e m

withForget :: Forget e e' => UnelabM e' a -> UnelabM e a
withForget (Unelab md) = Unelab (withReaderT forget md)

class Unelab t where
  type UnelabEnv t
  type Unelabed t

  unelab :: HasCallStack => t -> UnelabM (UnelabEnv t) (Unelabed t)


subunelab :: (Unelab t, Forget e (UnelabEnv t)) => t -> UnelabM e (Unelabed t)
subunelab = withForget . unelab

type UnelabMeta m = (Unelab m, UnelabEnv m ~ (), Unelabed m ~ Variable)

instance UnelabMeta m => Unelab (CdB (Tm m)) where
  type UnelabEnv (CdB (Tm m)) = Naming
  type Unelabed (CdB (Tm m)) = Raw
  unelab (CdB t' th) = local (nameSel th) $ unelab t'

instance Unelab Void where
  type UnelabEnv Void = ()
  type Unelabed Void = Variable
  unelab = absurd

instance Unelab DB where
  type UnelabEnv DB = Naming
  type Unelabed DB = Variable
  unelab (DB n) = Variable <$> do
    na@(ns, _, _) <- ask
    when (n >= length ns) $ throwError (InvalidNaming na)
    pure (ns <! n)

instance UnelabMeta m => Unelab (Tm m) where
  type UnelabEnv (Tm m) = Naming
  type Unelabed (Tm m) = Raw
  unelab = \case
    V -> ask >>= \case
           (B0 :< x, _, _) -> pure (Var (Variable x))
           na              -> throwError (VarOutOfScope na)
    A a -> pure (At a)
    P (s :<>: t) -> Cons <$> unelab s <*> unelab t
    (x := b) :. t -> Lam . uncurry (Scope . Hide) <$> case b of
            False -> ("_",) <$> unelab t
            True -> do
              na <- ask
              let y = freshen (unhide x) na
              local (`nameOn` y) $ (y,) <$> unelab t
    m :$ sg -> do
      sg <- unelab sg
      m <- Var <$> subunelab m
      pure $ case sg of
        B0 -> m
        _ -> Sbst sg m

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
        pure (sg :< Assign (Variable x) t)
      (sg :^^ w) -> case na of
        (_, th, _) | bigEnd th <= 0 -> throwError (UnexpectedEmptyThinning na)
        (xz, th, yz :< y) -> case thun th of
         (th, False) -> do
           sg <- local (const (xz, th, yz)) $ unelab (sg :^^ w)
           pure (sg :< Drop (Variable y))
         (th, True) ->
           case xz of
             xz :< x -> do
               sg <- local (const (xz, th, yz)) $ unelab (sg :^^ (w - 1))
               pure (sg :< Keep (Variable x))
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
    MP m th -> {- TODO: insert ThP -} pure (VarP (Variable m))
    HP -> pure UnderscoreP

instance Unelab (Pat, AActor) where
  type UnelabEnv (Pat, AActor) = DAEnv
  type Unelabed  (Pat, AActor) = (RawP, CActor)
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

instance Unelab Meta where
  type UnelabEnv Meta = ()
  type Unelabed Meta = Variable
  unelab m = pure (Variable $ '?' : show m)

instance Unelab ActorMeta where
  type UnelabEnv ActorMeta = ()
  type Unelabed ActorMeta = Variable
  unelab (ActorMeta str) = pure (Variable str)

instance Unelab Channel where
  type UnelabEnv Channel = ()
  type Unelabed Channel = Variable
  unelab (Channel str) = pure (Variable str)

instance Unelab JudgementForm where
  type UnelabEnv JudgementForm = ()
  type Unelabed JudgementForm = Variable
  unelab str = pure (Variable str)

instance Unelab Debug where
  type UnelabEnv Debug = ()
  type Unelabed Debug = Debug
  unelab = pure

instance Unelab AConnect where
  type UnelabEnv AConnect = ()
  type Unelabed AConnect = CConnect
  unelab (AConnect ch1 _ ch2 _) = CConnect <$> unelab ch1 <*> unelab ch2

instance Unelab Directive where
  type UnelabEnv Directive = ()
  type Unelabed Directive = Directive
  unelab = pure

instance Unelab t => Unelab (Format dir dbg t) where
  type UnelabEnv (Format dir dbg t) = UnelabEnv t
  type Unelabed (Format dir dbg t) = Format dir dbg (Unelabed t)
  unelab = \case
    TermPart d t -> TermPart d <$> unelab t
    DebugPart dbg -> pure (DebugPart dbg)
    StringPart str -> pure (StringPart str)

instance Unelab t => Unelab [Format dir dbg t] where
  type UnelabEnv [Format dir dbg t] = UnelabEnv t
  type Unelabed [Format dir dbg t] = [Format dir dbg (Unelabed t)]
  unelab = traverse unelab

instance Unelab AActor where
  type UnelabEnv AActor = DAEnv
  type Unelabed AActor = CActor
  unelab = \case
    a :|: b -> (:|:) <$> unelab a <*> unelab b
    Spawn jd ch a -> Spawn
        <$> subunelab jd
        <*> subunelab ch
        <*> local (declareChannel ch) (unelab a)
    Send ch tm a -> Send <$> subunelab ch <*> (inChannel ch $ subunelab tm) <*> unelab a
    Recv ch (av, a) -> Recv <$> subunelab ch <*> ((,) <$> subunelab av <*> unelab a)
    FreshMeta desc (av, a) -> FreshMeta <$> subunelab desc <*> ((,) <$> subunelab av <*> unelab a)
    Under (Scope x a) -> Under . Scope x <$> local (updateNaming (`nameOn` unhide x)) (unelab a)
    Push jd (p, t) a -> Push <$> subunelab jd <*> ((,) <$> subunelab p <*> subunelab t) <*> unelab a
    Lookup t (av, a) b -> Lookup <$> subunelab t <*> ((,) <$> subunelab av <*> unelab a) <*> unelab b
    Match tm pts -> Match <$> subunelab tm <*> traverse unelab pts
    Constrain s t -> Constrain <$> subunelab s <*> subunelab t
    Win -> pure Win
    Fail fmt -> Fail <$> traverse subunelab fmt
    Print fmt a -> Print <$> traverse subunelab fmt <*> unelab a
    Break fmt a -> Break <$> traverse subunelab fmt <*> unelab a
    Connect cnnct -> Connect <$> subunelab cnnct

instance Unelab Mode where
  type UnelabEnv Mode = ()
  type Unelabed Mode = Mode
  unelab = pure

instance Unelab () where
  type UnelabEnv () = ()
  type Unelabed () = ()
  unelab = pure

instance Unelab t => Unelab (JudgementStack t) where
  type UnelabEnv (JudgementStack t) = UnelabEnv t
  type Unelabed (JudgementStack t) = JudgementStack (Unelabed t)
  unelab = traverse unelab

instance Unelab t => Unelab (Protocol t) where
  type UnelabEnv (Protocol t) = UnelabEnv t
  type Unelabed (Protocol t) = Protocol (Unelabed t)
  unelab = traverse (traverse unelab)
