{-# LANGUAGE OverloadedStrings #-}

module Main where


import Control.Monad
import Data.Maybe

import System.Exit

import ANSI hiding (withANSI)
import Bwd
import Concrete.Base
import Doc (vcat, Config(..), Orientation(..))
import Doc.Render.Terminal
import Parse
import Actor
import Elaboration.Pretty()
import Machine
import Pretty
import Term.Base
import Options
import Command
import Machine.Trace (diagnostic, initTracing)

main :: IO ()
main = do
  opts <- getOptions
  txt <- readFile (filename opts)
  let ccs = parse pfile txt
  case elaborate ccs of
    Left err -> do
      putStrLn $ render (Config 80 Vertical) $
        vcat [ withANSI [ SetColour Background Red ] "Error" , pretty err ]
      exitFailure
    Right acs -> do
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs
      let p = Process (fromMaybe [] (tracingOption opts)) B0 initRoot (initEnv B0) initStore Win ""
      let (tr, res@(Process _ fs _ env sto Win _)) = run opts initTracing p acs
      unless (quiet opts) $ putStrLn $ diagnostic tr sto fs
      dmesg "" res `seq` pure ()
