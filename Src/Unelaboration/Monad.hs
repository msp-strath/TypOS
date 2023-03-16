{-# LANGUAGE ConstraintKinds #-}

module Unelaboration.Monad where

import Control.Monad.Except
import Control.Monad.Reader

import GHC.Stack

import Bwd
import Forget

import Actor (ActorMeta'(..), ActorMeta, Passport(..))
import Concrete.Base (Variable(..))
import Location (unknown)
import Term.Base (Meta, compressedMeta)
import Thin

------------------------------------------------------------------------
-- Naming

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

------------------------------------------------------------------------
-- Monad

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

------------------------------------------------------------------------
-- Class

class Unelab t where
  type UnelabEnv t
  type Unelabed t

  unelab :: HasCallStack => t -> UnelabM (UnelabEnv t) (Unelabed t)

subunelab :: (Unelab t, Forget e (UnelabEnv t)) => t -> UnelabM e (Unelabed t)
subunelab = withForget . unelab

------------------------------------------------------------------------
-- Unelaboration of meta variables

type UnelabMeta m = (Unelab m, UnelabEnv m ~ (), Unelabed m ~ Variable)

instance Unelab Meta where
  type UnelabEnv Meta = ()
  type Unelabed Meta = Variable
  unelab m = pure $ Variable unknown $ compressedMeta m

instance Unelab ActorMeta where
  type UnelabEnv ActorMeta = ()
  type Unelabed ActorMeta = Variable
  -- TODO: fixme
  unelab (ActorMeta ASubject str) = pure (Variable unknown $ "$" ++ str)
  unelab (ActorMeta _ str) = pure (Variable unknown str)
