module Options where

import Doc hiding (render)
import Doc.Render.Terminal
import Machine.Base
import Machine.Display()
import Options.Applicative
import Pretty

data Options = Options
  { filename :: String
  , tracingOption :: Maybe [MachineStep]
  }

options :: Parser Options
options = Options <$> argument str (metavar "FILE" <> showDefault <> value "examples/stlc.act" <> help "Actor file")
                  <*> (optional $ option (str >>= (readSteps . words))
                                             (long "tracing" <> metavar "LEVELS" <> help tracingHelp))
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
   levels = render 80 $ vcat $ map pretty [(minBound::MachineStep)..]
   exampleLevels = "\"" ++ render 0 (hsep $ map pretty [minBound::MachineStep, maxBound]) ++ "\""

getOptions :: IO Options
getOptions = execParser (info (options <**> helper)
                         (fullDesc <> progDesc "Execute actors in FILE"
                                       <> header "typOS - an operating system for typechecking processes"))
