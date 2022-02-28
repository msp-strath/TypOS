{-# LANGUAGE
  TypeSynonymInstances,
  PatternGuards,
  FlexibleContexts,
  GeneralizedNewtypeDeriving,
  ConstraintKinds #-}

module Display where

import Data.List

import Control.Monad.Except
import Control.Monad.Reader

import Bwd
import Thin
import ANSI
import Forget

import GHC.Stack

-- uglyprinting

type Naming =
  ( Bwd String  -- what's in the support
  , Th          -- and how that was chosen from
  , Bwd String  -- what's in scope
  )

data DisplayComplaint = UnexpectedEmptyThinning Naming
                      | VarOutOfScope Naming
                      | InvalidNaming Naming
                      | UnknownChannel String
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

instance Display () where
  type DisplayEnv () = ()
  display _ = pure "()"

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
