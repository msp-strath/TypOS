{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad

import System.Exit

import ANSI hiding (withANSI)
import qualified ANSI
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
import Machine.Trace (diagnostic, ldiagnostic)
import Utils

main :: IO ()
main = do
  opts <- getOptions
  txt <- readFile (filename opts)
  let ccs = parse pfile txt
  case elaborate ccs of
    Left err -> do
      putStrLn $ render (colours opts) (Config (termWidth opts) Vertical) $
        vcat [ withANSI [ SetColour Background Red ] "Error" , pretty err ]
      exitFailure
    Right (acs, table) -> do
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs
      let p = Process opts B0 initRoot (initEnv B0) initStore Win ""
      let res@(Process _ fs _ env sto Win _) = run opts p acs
      unless (quiet opts) $ putStrLn $ diagnostic opts sto fs
      whenJust (latex opts) $ \ file -> do
        writeFile file $ ldiagnostic table sto fs
        putStrLn (ANSI.withANSI [ SetColour Background Green ] "Success:" ++ " wrote latex derivation to " ++ file)
      dmesg "" res `seq` pure ()
