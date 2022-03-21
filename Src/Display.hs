{-# LANGUAGE ConstraintKinds, UndecidableInstances #-}

module Display where

import Data.List
import Data.Void

import Control.Monad.Except
import Control.Monad.Reader

import ANSI
import Bwd
import Concrete.Pretty ()
import Doc.Render.Terminal (render)
import Forget
import Format
import Pattern
import Thin

import Pretty (Pretty(..))
import Unelaboration (Unelab(..), evalUnelab, Naming)
import qualified Unelaboration

import GHC.Stack

-- uglyprinting

class Collapse t where
  collapse :: t String -> String

newtype BracesList t = BracesList { unBracesList :: [t] }

instance Collapse BracesList where
  collapse (BracesList strs) = "{" ++ intercalate "; " strs ++ "}"

instance Collapse Bwd where
  collapse strs = "[<" ++ intercalate ", " (strs <>> []) ++ "]"

instance Collapse [] where
  collapse strs = "[" ++ intercalate ", " strs ++ "]"

instance Collapse Cursor where
  collapse (lstrs :<+>: rstrs) =
    unwords [ collapse lstrs
            , withANSI [SetColour Foreground Red, SetWeight Bold] ":<+>:"
            , collapse rstrs
            ]

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

pdisplayDFT :: HasCallStack => Display t => t -> DisplayM (DisplayEnv t) String
pdisplayDFT t = do
  t' <- display t
  pure $ if ' ' `elem` t' then concat ["(", t', ")"] else t'

type Display0 m = (Display m, DisplayEnv m ~ ())
class Show t => Display t where
  type DisplayEnv t
  display :: HasCallStack => t -> DisplayM (DisplayEnv t) String

  pdisplay :: HasCallStack => t -> DisplayM (DisplayEnv t) String
  pdisplay = pdisplayDFT

subdisplay :: (Display t, Forget e (DisplayEnv t)) => t -> DisplayM e String
subdisplay = withForget . display

subpdisplay :: (Display t, Forget e (DisplayEnv t)) => t -> DisplayM e String
subpdisplay = withForget . pdisplay

viaPretty :: (Pretty (Unelabed t), Unelab t, UnelabEnv t ~ e) =>
             t -> DisplayM e String
viaPretty t = do
  env <- ask
  case evalUnelab env (unelab t) of
    Left err -> throwError (UnelabError err)
    Right t -> pure $ render (-1) $ pretty t

instance Display () where
  type DisplayEnv () = ()
  display _ = pure "()"

instance Display Void where
  type DisplayEnv Void = ()
  display = absurd

instance Display DB where
  type DisplayEnv DB = Naming
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display [Format () String t] where
  type DisplayEnv [Format () String t] = UnelabEnv t
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display [Format Directive Debug t] where
  type DisplayEnv [Format Directive Debug t] = UnelabEnv t
  display = viaPretty

instance Display Pat where
  type DisplayEnv Pat = Naming
  display = viaPretty
