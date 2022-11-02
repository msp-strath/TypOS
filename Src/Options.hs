{-# LANGUAGE OverloadedStrings #-}
{- | Description: 

-}
module Options where

-- from the optparse-applicative package
import Options.Applicative 
import System.Console.Terminal.Size (size, width)
import System.Environment (getEnv)

import qualified ANSI
import Machine.Steps
import Pretty (Pretty(pretty),Annotations,render,vcat,hsep,toANSIs)
import qualified Text.PrettyPrint.Compact as Compact

data Options = Options
  { filename :: String
  , wAll :: Bool
  , quiet :: Bool
  , colours :: Bool
  , tracingOption :: Maybe [MachineStep]
  , latex :: Maybe FilePath
  , latexAnimated :: Maybe FilePath
  , termWidth :: Int
  , noContext :: Bool
  } deriving (Show)

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
 where
   readSteps :: [String] -> ReadM [MachineStep]
   readSteps = mapM $ \case
     "recv" -> pure MachineRecv
     "send" -> pure MachineSend
     "exec" -> pure MachineExec
     "move" -> pure MachineMove
     "unify" -> pure MachineUnify
     "break" -> pure MachineBreak
     "clause" -> pure MachineClause
     x -> readerError $ "Unknown tracing level '" ++ x ++ "'. Accepted levels:\n" ++ levels
   tracingHelp = "Override tracing level (combinations of {" ++ levels ++ "} in quotes, separated by spaces, e.g. " ++ exampleLevels ++ ")"
   levels = render $ vcat $ map pretty [(minBound::MachineStep)..]
   exampleLevels = "\"" ++ render (hsep $ map pretty [minBound::MachineStep, maxBound]) ++ "\""

getOptions :: IO Options
getOptions = do
  opts <- execParser (info (poptions <**> helper)
                     (fullDesc <> progDesc "Execute actors in FILE"
                               <> header "typOS - an operating system for typechecking processes"))
  termSize <- size
  let w = maybe 80 width termSize
  pure $ opts { termWidth = w }

isTermDumb :: IO Bool
isTermDumb = ("dumb"==) <$> getEnv "TERM"

renderOptions :: Options -> Compact.Options Annotations String
renderOptions opts = Compact.Options
  { optsPageWidth = termWidth opts
  , optsAnnotate = \ ann str ->
      if colours opts then ANSI.withANSI (toANSIs ann) str else str
  }
