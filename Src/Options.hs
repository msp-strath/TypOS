{-# LANGUAGE OverloadedStrings #-}

module Options where

import Options.Applicative
import System.Console.Terminal.Size (size, width)
import System.Environment (getEnv)

import Doc
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
  , latex :: Maybe FilePath
  , termWidth :: Int
  , noContext :: Bool
  } deriving (Show)

poptions :: Parser Options
poptions = Options
  <$> argument str (metavar "FILE" <> showDefault <> value "examples/stlc.act" <> help "Actor file")
  <*> flag False True (short 'q' <> long "quiet" <> help "Silence tracing")
  <*> flag True False (long "no-colour" <> help "Do not use colours in the output")
  <*> (optional $ option (str >>= (readSteps . words))
                         (long "tracing" <> metavar "LEVELS" <> help tracingHelp))
  <*> optional (option str (metavar "FILE" <> long "latex" <> help "Output LaTeX derivation to file"))
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
     x -> readerError $ "Unknown tracing level '" ++ x ++ "'. Accepted levels:\n" ++ levels
   tracingHelp = "Override tracing level (combinations of {" ++ levels ++ "} in quotes, separated by spaces, e.g. " ++ exampleLevels ++ ")"
   levels = show $ vcat $ map pretty [(minBound::MachineStep)..]
   exampleLevels = "\"" ++ show (hsep $ map pretty [minBound::MachineStep, maxBound]) ++ "\""

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

