{-# LANGUAGE OverloadedStrings #-}
{- | Description: The various options that can be given on the command line

  Also stores whether the terminal is dumb, which is an "environment option"
-}
module Options where

-- from the optparse-applicative package
import Options.Applicative -- needs lots from here

import System.Console.Terminal.Size (size, width)
import System.Environment (getEnv)

import qualified ANSI
import Machine.Steps (MachineStep(..), readSteps, tracingHelp)
import Pretty (Annotations,toANSIs)
import qualified Text.PrettyPrint.Compact as Compact

-- | The Options that can be specified
data Options = Options
  { filename :: String                   -- Actor file
  , wAll :: Bool                         -- turn on (All) warnings
  , quiet :: Bool                        -- be quiet when working
  , colours :: Bool                      -- colour output?
  , tracingOption :: Maybe [MachineStep] -- which machine steps to trace?
  , latex :: Maybe FilePath              -- where to put the latex output
  , latexAnimated :: Maybe FilePath      -- where to put the animated latex output
  , termWidth :: Int                     -- width of terminal to assume
  , noContext :: Bool                    -- Do not print file context of errors
  } deriving (Show)

-- | A partially-filled 'Options' that is not actually safe to use 'raw'.
-- In theory, shouldn't be exported from here, but it is used...
unsafeOptions :: Options
unsafeOptions = Options
 { filename = ""
 , wAll = True
 , quiet = False
 , colours = True
 , tracingOption = Nothing
 , latex = Nothing
 , latexAnimated = Nothing
 , termWidth = 80
 , noContext = False
 }

-- | Parse our options.
poptions :: Parser Options
poptions = Options
  <$> argument str (metavar "FILE" <> completer (bashCompleter "file") <> help "Actor file")
  <*> flag False True (long "wAll" <> help "Print all warnings")
  <*> flag False True (short 'q' <> long "quiet" <> help "Silence tracing")
  <*> flag True False (long "no-colour" <> help "Do not use colours in the output")
  <*> (optional $ option (str >>= (readSteps . words))
                         (long "tracing" <> metavar "LEVELS" <> help tracingHelp))
  <*> optional (option str (metavar "FILE" <> long "latex" <> completer (bashCompleter "file") <> help "Output LaTeX derivation to FILE"))
  <*> optional (option str (metavar "FILE" <> long "latex-animated" <> completer (bashCompleter "file") <> help "Output animated LaTeX derivation to FILE"))
  <*> pure 80 -- dummy value
  <*> flag False True (long "no-context" <> help "Do not print file context of errors")

-- | Actually get the actions
getOptions :: IO Options
getOptions = do
  opts <- execParser (info (poptions <**> helper)
                     (fullDesc <> progDesc "Execute actors in FILE"
                               <> header "typOS - an operating system for typechecking processes"))
  termSize <- size
  let w = maybe 80 width termSize
  pure $ opts { termWidth = w }

-- | Is the terminal in which we're currently running "dumb" ?
isTermDumb :: IO Bool
isTermDumb = ("dumb"==) <$> getEnv "TERM"

-- | for creating the first argument to 'renderWith'
renderOptions :: Options -> Compact.Options Annotations String
renderOptions opts = Compact.Options
  { optsPageWidth = termWidth opts
  , optsAnnotate = \ ann str ->
      if colours opts then ANSI.withANSI (toANSIs ann) str else str
  }
