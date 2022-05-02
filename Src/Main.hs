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
import Display (unsafeEvalDisplay)
import Location

main :: IO ()
main = do
  opts <- getOptions
  let cfg = Config (termWidth opts) Vertical
  txt <- readFile (filename opts)
  let ccs = parse pfile (Source txt $ initLocation (filename opts))
  case elaborate ccs of
    Left err -> do
      putStrLn $ render (colours opts) cfg $
        vcat [ withANSI [ SetColour Background Red ] "Error" , pretty err ]
      exitFailure
    Right (acs, table) -> do
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs
      let p = Process opts B0 initRoot (initEnv B0) initStore (Win unknown) ""
      let res@(Process _ fs _ env sto a _) = run opts p acs
      unless (isWin a) $ do
         putStrLn $ ANSI.withANSI [SetColour Background Red] "Error: Did not win"
         putStrLn $ let (_, _, _, a) = unsafeEvalDisplay initDEnv $ displayProcess' p in
                    render (colours $ options p) cfg a
      unless (quiet opts) $ putStrLn $ diagnostic opts sto fs
      whenJust (latex opts) $ \ file -> do
        writeFile file $ ldiagnostic table sto fs
        putStrLn (ANSI.withANSI [ SetColour Background Green ] "Success:" ++ " wrote latex derivation to " ++ file)
      dmesg "" res `seq` pure ()
