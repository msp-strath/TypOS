module Alarm where

import Control.Monad (guard)
import Data.Functor (($>))
import System.IO.Unsafe (unsafePerformIO)

import ANSI
import Options
import Utils

alarm :: Options -> String -> a -> a
alarm opts str x = unsafePerformIO $ do
  putStrLn $
    withANSI (guard (colours opts) $> SetColour Background Red) $
    "Alarm:" ++ ' ' : str
  -- Check if terminal can give us input before asking for it
  unlessM isTermDumb (() <$ getLine)
  pure x
