{-# LANGUAGE ConstraintKinds #-}

module Unelaboration where

import Control.Monad.Except
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Void

import Actor
import Bwd
import Concrete.Base
import Forget
import Format
import Hide
import Pattern
import Scope
import Syntax()
import Semantics()
import Term.Base
import Thin
import Location (unknown)
import Unelaboration.Monad

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
  unelab (DB n) = Variable unknown <$> do
    na@(ns, _, _) <- ask
    when (n >= length ns) $ throwError (InvalidNaming na)
    pure (ns <! n)

instance UnelabMeta m => Unelab (Tm m) where
  type UnelabEnv (Tm m) = Naming
  type Unelabed (Tm m) = Raw
  unelab = \case
    V -> ask >>= \case
           (B0 :< x, _, _) -> pure (Var unknown (Variable unknown x))
           na              -> throwError (VarOutOfScope na)
    A a -> pure (At unknown a)
    P Cell (s :<>: t) -> Cons unknown <$> unelab s <*> unelab t
    P Oper (s :<>: t) -> Op unknown <$> unelab s <*> unelab t
    (x := b) :. t -> Lam unknown . uncurry (Scope . Hide) <$> case b of
            False -> (Unused,) <$> unelab t
            True -> do
              na <- ask
              let y = freshen (unhide x) na
              local (`nameOn` y) $ (Used (Variable unknown y),) <$> unelab t
    m :$ sg -> do
      sg <- unelab sg
      m <- Var unknown <$> subunelab m
      pure $ case sg of
        B0 -> m
        _ -> Sbst unknown sg m
    G g t -> Guarded g <$> unelab t

instance UnelabMeta m => Unelab (Sbst m) where
  type UnelabEnv (Sbst m) = Naming
  type Unelabed (Sbst m) = Bwd Assign
  unelab sg = do
    na@(_, th, _) <- ask
    case sg of
      (S0 :^^ _) | th == ones (bigEnd th) -> pure B0
      (ST (CdB sg th :<>: CdB (Hide x := t) ph) :^^ 0) -> do
        t <- unelab (CdB t ph)
        sg <- local (nameSel th) $ unelab sg
        pure (sg :< Assign unknown (Variable unknown x) t)
      (sg :^^ w) -> case na of
        (_, th, _) | bigEnd th <= 0 -> throwError (UnexpectedEmptyThinning na)
        (xz, th, yz :< y) -> case thun th of
         (th, False) -> do
           local (const (xz, th, yz)) $ unelab (sg :^^ w)
           {- TODO: bring back printing of Drop?
           sg <- local (const (xz, th, yz)) $ unelab (sg :^^ w)
           pure (sg :< Drop unknown (Variable unknown y))
           -}
         (th, True) ->
           case xz of
             xz :< x -> do
               local (const (xz, th, yz)) $ unelab (sg :^^ (w - 1))
             _ -> throwError $ InvalidNaming na
        _ -> throwError $ InvalidNaming na

instance Unelab Pat where
  type UnelabEnv Pat = Naming
  type Unelabed Pat = RawP
  unelab = \case
    AT x p -> AsP unknown <$> subunelab x <*> unelab p
    VP n -> VarP unknown <$> unelab n
    AP str -> pure (AtP unknown str)
    PP p q -> ConsP unknown <$> unelab p <*> unelab q
    BP x p -> do
      p <- local (`nameOn` unhide x) (unelab p)
      pure (LamP unknown (Scope (mkBinder . Variable unknown <$> x) p))
    MP m th -> {- TODO: insert ThP -} VarP unknown <$> subunelab m
    HP -> pure (UnderscoreP unknown)

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


instance Unelab (Binder ActorMeta) where
  type UnelabEnv (Binder ActorMeta) = ()
  type Unelabed (Binder ActorMeta) = RawP
  unelab Unused = pure (UnderscoreP unknown)
  unelab (Used av) = VarP unknown <$> unelab av

instance Unelab Channel where
  type UnelabEnv Channel = ()
  type Unelabed Channel = Variable
  unelab (Channel str) = pure (Variable unknown str)

instance Unelab Stack where
  type UnelabEnv Stack = ()
  type Unelabed Stack = Variable
  unelab (Stack str) = pure (Variable unknown str)

instance Unelab JudgementName where
  type UnelabEnv JudgementName = ()
  type Unelabed JudgementName = Variable
  unelab str = pure (Variable unknown str)

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

instance Unelab AScrutinee where
  type UnelabEnv AScrutinee = Naming
  type Unelabed AScrutinee = CScrutinee
  unelab = \case
    SubjectVar r t -> do
      v <- unelab t
      case v of
        -- Sbst _ _ (Var r m) -> pure (ActorVar r m)
        Var r m -> pure (SubjectVar r m)
    Pair r s t -> Pair r <$> unelab s <*> unelab t
    Lookup r stk t -> do
      stk <- subunelab stk
      t <- unelab t >>= \case
        -- Sbst _ _ (Var r m) -> pure m
        Var r m -> pure m
      pure $ Lookup r stk t
    Compare r s t -> Compare r <$> unelab s <*> unelab t
    Term r t -> Term r <$> unelab t

instance Unelab AActor where
  type UnelabEnv AActor = DAEnv
  type Unelabed AActor = CActor
  unelab = \case
    Branch r a b -> Branch r <$> unelab a <*> unelab b
    Spawn r em jd ch a -> Spawn r em
        <$> subunelab jd
        <*> subunelab ch
        <*> local (declareChannel ch) (unelab a)
    Send r ch gd tm a -> Send r <$> subunelab ch <*> pure () <*> inChannel ch (subunelab tm) <*> unelab a
    Recv r ch (av, a) -> Recv r <$> subunelab ch <*> ((,) <$> subunelab av <*> unelab a)
    FreshMeta r desc (av, a) -> FreshMeta r <$> subunelab desc <*> ((,) <$> subunelab av <*> unelab a)
    Let r av desc t a -> Let r <$> subunelab av <*> subunelab desc <*> subunelab t <*> unelab a
    Under r mty (Scope x a) ->
      Under r <$> traverse subunelab mty
              <*> (Scope x <$> local (updateNaming (`nameOn` getVariable (unhide x))) (unelab a))
    Push r stk (p, _, t) a -> Push r <$> subunelab stk <*> ((,(),) <$> subunelab p <*> subunelab t) <*> unelab a
    Match r tm pts -> Match r <$> subunelab tm <*> traverse unelab pts
    Constrain r s t -> Constrain r <$> subunelab s <*> subunelab t
    Win r -> pure (Win r)
    Fail r fmt -> Fail r <$> traverse subunelab fmt
    Print r fmt a -> Print r <$> traverse subunelab fmt <*> unelab a
    Break r fmt a -> Break r <$> traverse subunelab fmt <*> unelab a
    Connect r cnnct -> Connect r <$> subunelab cnnct
    Note r a -> Note r <$> unelab a

instance Unelab t => Unelab (Mode t) where
  type UnelabEnv (Mode t) = UnelabEnv t
  type Unelabed (Mode t) = Mode (Unelabed t)
  unelab = traverse unelab

instance Unelab () where
  type UnelabEnv () = ()
  type Unelabed () = ()
  unelab = pure

instance (Unelab k, Unelab v, UnelabEnv k ~ UnelabEnv v) => Unelab (ContextStack k v) where
  type UnelabEnv (ContextStack k v) = UnelabEnv k
  type Unelabed (ContextStack k v) = ContextStack (Unelabed k) (Unelabed v)
  unelab (ContextStack k v) = ContextStack <$> unelab k <*> unelab v

instance Unelab AProtocol where
  type UnelabEnv AProtocol = Naming
  type Unelabed AProtocol = CProtocol
  unelab (Protocol ps) = Protocol <$> traverse f ps
    where
      f (m, s) = (,) <$> unelab m <*> unelab s
