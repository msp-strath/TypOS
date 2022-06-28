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
import Doc (Config(..), Orientation(..), flush, vcat)
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
import qualified Data.Map as Map
import Data.Maybe (isNothing)
import Data.List (intercalate)

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
    Right (ws, acs, table) -> do
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs

      -- Elaboration warnings
      unless ((quiet opts && not (wAll opts)) || null ws) $ do
        putStrLn $ render (colours opts) cfg $ vcat $ map pretty ws

      let p = Process opts B0 initRoot (initEnv B0) initStore (Win unknown) []
      let res@(Process _ fs _ env sto a _) = run opts p acs

      -- Failed run error
      unless (isWin a) $ do
         putStrLn $ ANSI.withANSI [SetColour Background Red] "Error:" ++ " Did not win"
         putStrLn $ let (_, _, _, a) = unsafeEvalDisplay initDEnv $ displayProcess' res in
                    render (colours $ options p) cfg a

      -- Unsolved metas warning
      let unsolved = Map.mapMaybe (\ (_, msol)  -> () <$ guard (isNothing msol)) $ solutions sto
      case Map.keys unsolved of
        [] -> pure ()
        ms -> putStrLn $ ANSI.withANSI [SetColour Background Yellow] "Warning:"
                      ++ " Unsolved meta" ++ (if length ms > 1 then "s" else "")
                      ++ " (" ++ intercalate ", " (show <$> ms) ++ ")"

      -- Resulting derivation
      unless (quiet opts) $ do
        putStrLn $ diagnostic opts sto fs

      -- LaTeX & beamer backends
      whenJust (latex opts) $ \ file -> do
        writeFile file $ ldiagnostic table sto fs
        putStrLn $ ANSI.withANSI [ SetColour Background Green ] "Success:"
                ++ " wrote latex derivation to " ++ file
      whenJust (latexAnimated opts) $ \ file -> do
        writeFile file $ adiagnostic table sto fs (logs res)
        putStrLn $ ANSI.withANSI [ SetColour Background Green ] "Success:"
                ++ " wrote animated latex derivation to " ++ file
      dmesg "" res `seq` pure ()
