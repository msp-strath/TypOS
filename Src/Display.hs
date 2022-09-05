{-# LANGUAGE ConstraintKinds, UndecidableInstances #-}

module Display where

import Data.Void

import Control.Monad.Except
import Control.Monad.Reader

import Actor
import Concrete.Pretty ()
import Forget
import Format
import Options
import Doc hiding (render)
import Doc.Render.Terminal
import Thin

import Pretty (Pretty(..))
import Unelaboration (Unelab(..), evalUnelab, Naming)
import qualified Unelaboration

import GHC.Stack

-- uglyprinting

data DisplayComplaint
  = UnexpectedEmptyThinning Naming
  | VarOutOfScope Naming
  | InvalidNaming Naming
  | UnknownChannel String
  | UnelabError Unelaboration.Complaint
  deriving (Show)

newtype DisplayM e a = Display
  { runDisplay :: (ReaderT e
                  (Either DisplayComplaint))
                  a }
  deriving ( Functor, Applicative, Monad
           , MonadError DisplayComplaint
           , MonadReader e)

withEnv :: e' -> DisplayM e' a -> DisplayM e a
withEnv rh (Display md) = Display (withReaderT (const rh) md)

withForget :: Forget e e' => DisplayM e' a -> DisplayM e a
withForget (Display md) = Display (withReaderT forget md)

evalDisplay :: e -> DisplayM e a -> Either DisplayComplaint a
evalDisplay e = (`runReaderT` e)
              . runDisplay

unsafeEvalDisplay :: e -> DisplayM e a -> a
unsafeEvalDisplay e = either (error . show) id . evalDisplay e

type Display0 m = (Display m, DisplayEnv m ~ ())
class Show t => Display t where
  type DisplayEnv t
  display :: HasCallStack => t -> DisplayM (DisplayEnv t) (Doc Annotations)
  displayPrec :: HasCallStack => Int -> t -> DisplayM (DisplayEnv t) (Doc Annotations)

  display = displayPrec 0
  displayPrec _ = display

pdisplay :: Display t => t -> DisplayM (DisplayEnv t) (Doc Annotations)
pdisplay = displayPrec 1

subdisplay :: (Display t, Forget e (DisplayEnv t)) => t -> DisplayM e (Doc Annotations)
subdisplay = withForget . display

subpdisplay :: (Display t, Forget e (DisplayEnv t)) => t -> DisplayM e (Doc Annotations)
subpdisplay = withForget . pdisplay

viaPretty :: (Pretty (Unelabed t), Unelab t, UnelabEnv t ~ e) =>
             t -> DisplayM e (Doc Annotations)
viaPretty t = do
  env <- ask
  case evalUnelab env (unelab t) of
    Left err -> throwError (UnelabError err)
    Right t -> pure $ pretty t

instance Display () where
  type DisplayEnv () = ()
  display = viaPretty

instance Display Void where
  type DisplayEnv Void = ()
  display = viaPretty

instance Display DB where
  type DisplayEnv DB = Naming
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display [Format () (Doc Annotations) t] where
  type DisplayEnv [Format () (Doc Annotations) t] = UnelabEnv t
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display [Format Directive Debug t] where
  type DisplayEnv [Format Directive Debug t] = UnelabEnv t
  display = viaPretty

instance Display Pat where
  type DisplayEnv Pat = Naming
  display = viaPretty

unsafeDocDisplayClosed :: (DisplayEnv a ~ Naming, Display a) => Options -> a -> Doc Annotations
unsafeDocDisplayClosed opts t
  = unsafeEvalDisplay Unelaboration.initNaming
  $ display t

unsafeDisplayClosed :: (DisplayEnv a ~ Naming, Display a) => Options -> a -> String
unsafeDisplayClosed opts t
  = render (colours opts) (Config (termWidth opts) Vertical)
  $ unsafeDocDisplayClosed opts t
