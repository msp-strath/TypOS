module Options where

import Doc hiding (render)
import Doc.Render.Terminal
import Machine.Base
import Machine.Display()
import Options.Applicative
import Pretty

data Options = Options
  { filename :: String
  , quiet :: Bool
  , tracingOption :: Maybe [MachineStep]
  , latex :: Maybe FilePath
  }

options :: Parser Options
options = Options
  <$> argument str (metavar "FILE" <> showDefault <> value "examples/stlc.act" <> help "Actor file")
  <*> flag False True (short 'q' <> long "quiet" <> help "Silence tracing")
  <*> (optional $ option (str >>= (readSteps . words))
                         (long "tracing" <> metavar "LEVELS" <> help tracingHelp))
  <*> optional (option str (metavar "FILE" <> long "latex" <> help "Output LaTeX derivation to file"))
 where
   readSteps :: [String] -> ReadM [MachineStep]
   readSteps = mapM $ \case
     "recv" -> pure MachineRecv
     "send" -> pure MachineSend
     "exec" -> pure MachineExec
     "move" -> pure MachineMove
     "unify" -> pure MachineUnify
     "break" -> pure MachineBreak
     x -> readerError $ "Unknown tracing level '" ++ x ++ "'. Accepted levels: " ++ levels
   tracingHelp = "Override tracing level (combinations of {" ++ levels ++ "} in quotes, separated by spaces, e.g. " ++ exampleLevels ++ ")"
   levels = render (initConfig 80) $ vcat $ map pretty [(minBound::MachineStep)..]
   exampleLevels = "\"" ++ render (initConfig 0) (hsep $ map pretty [minBound::MachineStep, maxBound]) ++ "\""

getOptions :: IO Options
getOptions = execParser (info (options <**> helper)
                         (fullDesc <> progDesc "Execute actors in FILE"
                                       <> header "typOS - an operating system for typechecking processes"))
