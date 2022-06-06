{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad

import Data.Foldable (fold)

import System.Exit
import System.FilePath (takeExtension)

import ANSI hiding (withANSI)
import qualified ANSI
import Bwd
import Concrete.Base
import Doc (Config(..), Orientation(..), flush)
import Doc.Render.Terminal
import Parse
import Actor
import Elaboration.Pretty()
import Machine
import Pretty
import Term.Base
import Options
import Command
import Machine.Trace (diagnostic, ldiagnostic, adiagnostic)
import Utils
import Display (unsafeEvalDisplay)
import Location

main :: IO ()
main = do
  opts <- getOptions
  let cfg = Config (termWidth opts) Vertical
  txt <- readFile (filename opts)
  let parser = case takeExtension (filename opts) of
                 ".md" -> pmarkdown
                 _ -> pfile
  let ccs = parse parser (Source txt $ initLocation (filename opts))
  case elaborate ccs of
    Left err -> do
      ctxt <- if noContext opts then pure "" else fileContext (getRange err)
      putStrLn $ render (colours opts) cfg $ fold
        [ flush (withANSI [ SetColour Background Red ] "Error") <> ctxt
        , pretty err
        ]
      exitFailure
    Right (acs, table) -> do
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs
      let p = Process opts B0 initRoot (initEnv B0) initStore (Win unknown) []
      let res@(Process _ fs _ env sto a _) = run opts p acs
      unless (isWin a) $ do
         putStrLn $ ANSI.withANSI [SetColour Background Red] "Error: Did not win"
         putStrLn $ let (_, _, _, a) = unsafeEvalDisplay initDEnv $ displayProcess' p in
                    render (colours $ options p) cfg a
      unless (quiet opts) $ putStrLn $ diagnostic opts sto fs
      whenJust (latex opts) $ \ file -> do
        writeFile file $ adiagnostic table sto fs (logs res)
        putStrLn (ANSI.withANSI [ SetColour Background Green ] "Success:" ++ " wrote latex derivation to " ++ file)
      dmesg "" res `seq` pure ()
