{-# LANGUAGE
  TypeSynonymInstances,
  PatternGuards,
  GeneralizedNewtypeDeriving
  #-}

module Display where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad.Except
import Control.Monad.Reader

import Bwd
import Thin
import ANSI


-- uglyprinting

data DisplayEnv = DEnv { naming :: Naming
                       , chNaming :: (Map String Naming)
                       }

type Naming =
  ( Bwd String  -- what's in the support
  , Th          -- and how that was chosen from
  , Bwd String  -- what's in scope
  )

data DisplayComplaint = UnexpectedEmptyThinning Naming
                      | VarOutOfScope Naming
                      | InvalidNaming Naming
  deriving (Show)

newtype DisplayM a = Display
  { runDisplay :: (ReaderT DisplayEnv
                  (Either DisplayComplaint))
                  a }
  deriving ( Functor, Applicative, Monad
           , MonadError DisplayComplaint
           , MonadReader DisplayEnv)

evalDisplay :: DisplayM a -> Either DisplayComplaint a
evalDisplay = (`runReaderT` initDisplay)
            . runDisplay

unsafeEvalDisplay :: DisplayM a -> a
unsafeEvalDisplay = either (error . show) id . evalDisplay

initNaming :: Naming
initNaming = (B0, ones 0, B0)

initDisplay :: DisplayEnv
initDisplay = DEnv initNaming Map.empty

-- The point is that when we reach a metavariable,
-- we have to document its permitted dependencies.

setNaming :: Naming -> DisplayEnv -> DisplayEnv
setNaming na (DEnv _ chs) = DEnv na chs

declareChannel :: String -> DisplayEnv -> DisplayEnv
declareChannel ch (DEnv na chs) = DEnv na (Map.insert ch na chs)

nameSel :: Th -> DisplayEnv -> DisplayEnv
nameSel th (DEnv (xz, ph, yz) chs) = DEnv (th ?< xz, th <^> ph, yz) chs

nameOn :: DisplayEnv -> String -> DisplayEnv
nameOn (DEnv (xz, th, yz) chs) x = DEnv (xz :< x, th -? True, yz :< x) chs

freshen :: String -> Naming -> String
freshen x (xz, _, _) = head [y | y <- ys, all (y /=) xz] where
  ys = x : [x ++ show (i :: Integer) | i <- [0..]]

pdisplayDFT :: Display t => t -> DisplayM String
pdisplayDFT t = do
  t' <- display t
  pure $ if ' ' `elem` t' then concat ["(", t', ")"] else t'

class Show t => Display t where
  display :: t -> DisplayM String

  pdisplay :: t -> DisplayM String
  pdisplay = pdisplayDFT

display0 :: Display t => t -> DisplayM String
display0 t = local (setNaming initNaming) $ display t

instance Display () where
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
