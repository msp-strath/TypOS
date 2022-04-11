{-# LANGUAGE OverloadedStrings #-}

module Options where

import Doc
import Options.Applicative
import Pretty

data MachineStep
  = MachineRecv
  | MachineSend
  | MachineExec
  | MachineMove
  | MachineUnify
  | MachineBreak
  deriving (Eq, Show, Enum, Bounded)

instance Pretty MachineStep where
  pretty = \case
    MachineRecv -> "recv"
    MachineSend -> "send"
    MachineExec -> "exec"
    MachineMove -> "move"
    MachineUnify -> "unify"
    MachineBreak -> "break"

data Options = Options
  { filename :: String
  , quiet :: Bool
  , colours :: Bool
  , tracingOption :: Maybe [MachineStep]
  } deriving (Show)

poptions :: Parser Options
poptions = Options
  <$> argument str (metavar "FILE" <> showDefault <> value "examples/stlc.act" <> help "Actor file")
  <*> flag False True (short 'q' <> long "quiet" <> help "Silence tracing")
  <*> flag True False (long "no-colour" <> help "Do not use colours in the output")
  <*> optional (option (str >>= readSteps . words)
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
   levels = show $ vcat $ map pretty [(minBound::MachineStep)..]
   exampleLevels = "\"" ++ show (hsep $ map pretty [minBound::MachineStep, maxBound]) ++ "\""

getOptions :: IO Options
getOptions = execParser (info (poptions <**> helper)
                         (fullDesc <> progDesc "Execute actors in FILE"
                                       <> header "typOS - an operating system for typechecking processes"))
