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
import Location
import qualified Data.Map as Map
import Data.Maybe (isNothing)
import Data.List (intercalate)

main :: IO ()
main = do
  opts <- getOptions
  txt <- readFile (filename opts)
  let parser = case takeExtension (filename opts) of
                 ".md" -> pmarkdown
                 _ -> pfile
  let ccs = parse parser (Source txt $ initLocation (filename opts))
  case elaborate ccs of
    Left err -> do
      ctxt <- if noContext opts then pure "" else fileContext (getRange err)
      putStrLn $ renderWith (renderOptions opts) $ fold
        [ flush (withANSI [ SetColour Background Red ] "Error") <> ctxt
        , pretty err
        ]
      exitFailure
    Right (ws, acs, table) -> do
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs

      -- Elaboration warnings
      unless ((quiet opts && not (wAll opts)) || null ws) $ do
        putStrLn $ renderWith (renderOptions opts) $ vcat $ map pretty ws

      let p = Process opts B0 initRoot (initEnv B0) initStore (Win unknown) [] initRoot
      let res@(Process _ fs _ env sto a _ geas) = run opts p acs

      -- TODO: eventually need to be more careful about the operators due to local extensions
      let dat = HeadUpData (mkOpTable (B0 <>< fs)) sto (opts {quiet = True}) env

      -- run diagnostics
      let (win, trace) = diagnostic opts dat fs

      -- Failed run error
      unless win $ do
         putStrLn $ anerror opts $ " Did not win"
         -- putStrLn $ let (_, _, _, a) = unsafeEvalDisplay initDEnv $ displayProcess' res in
         --   renderWith (renderOptions $ options p) a

      -- Unsolved metas warning
      let unsolved = Map.mapMaybe (\ (_, msol)  -> () <$ guard (isNothing msol)) $ solutions sto
      case Map.keys unsolved of
        [] -> pure ()
        ms -> putStrLn $ warning opts
            $ " Unsolved meta" ++ (if length ms > 1 then "s" else "")
            ++ " (" ++ intercalate ", " (show <$> ms) ++ ")"

      -- Resulting derivation
      unless (quiet opts) $ do
        putStrLn trace

      -- LaTeX & beamer backends
      whenJust (latex opts) $ \ file -> do
        writeFile file $ ldiagnostic table dat fs
        putStrLn $ success opts $ " wrote latex derivation to " ++ file
      whenJust (latexAnimated opts) $ \ file -> do
        writeFile file $ adiagnostic table dat fs (logs res)
        putStrLn $ success opts $ " wrote animated latex derivation to " ++ file
      dmesg "" res `seq` pure ()

      unless win $ exitFailure

label :: Colour -> String -> Options -> String -> String
label col lbl opts str =
  ANSI.withANSI (SetColour Background Yellow <$ guard (colours opts)) (lbl ++ ":")
  ++ str

warning = label Yellow "Warning"
success = label Green "Success"
anerror = label Red "Error"
