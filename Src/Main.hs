{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.Maybe

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

main :: IO ()
main = do
  opts <- getOptions
  txt <- readFile (filename opts)
  let ccs = parse pfile txt
  acs <- case elaborate ccs of
    Left err -> do error $ render (Config 80 Vertical) $
                     vcat [ withANSI [ SetColour Background Red ] "Error"
                          , pretty err ]

    Right acs -> pure acs
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs
  let p = Process (fromMaybe [] (tracingOption opts)) B0 initRoot (initEnv B0) initStore Win ""
  let res@(Process _ fs _ env sto Win _) = run opts p acs
  dmesg "" res `seq` pure ()
