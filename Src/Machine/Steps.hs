{-# LANGUAGE OverloadedStrings #-}
{- | Description: 

-}
module Machine.Steps (
    MachineStep(..)
  , readSteps , tracingHelp
  ) where

import Options.Applicative (ReadM, readerError)
import Data.Tuple (swap)

import Pretty (Pretty(pretty), text, render, vcat, Doc, Annotations, hsep)

-- | Define the steps that the machine can take
data MachineStep
  = MachineRecv
  | MachineSend
  | MachineExec
  | MachineMove
  | MachineUnify
  | MachineBreak
  | MachineClause
  deriving (Eq, Show, Enum, Bounded)

-- | Pair up 'MachineStep' with its 'String'
namesOfSteps :: [(MachineStep, String)]
namesOfSteps =
  [ ( MachineRecv , "recv")
  , ( MachineSend , "send")
  , ( MachineExec , "exec")
  , ( MachineMove , "move")
  , ( MachineUnify , "unify")
  , ( MachineBreak , "break")
  , ( MachineClause , "clause")
  ]

-- | Output 'MachineStep' in a way that's nicer for humans
instance Pretty MachineStep where
  pretty m = case (lookup m namesOfSteps) of
    Just n -> text n
    Nothing -> error "impossible: a MachineStep has no name?"

-- | What are the steps that the machine can take?
theSteps :: [Doc Annotations]
theSteps = map (text.snd) namesOfSteps

-- | Read a single step
aStep :: String -> ReadM MachineStep
aStep s = case lookup s (map swap namesOfSteps) of
  Just x -> pure x
  Nothing -> readerError $ "Unknown tracing level '" ++ s ++ "'. " ++ allowedLevels
    where
       allowedLevels = "Accepted levels:\n" ++ (render . vcat $ theSteps)

-- | Read all the steps to trace
readSteps :: [String] -> ReadM [MachineStep]
readSteps = mapM aStep

-- | String to print out to let users know what tracing levels there are
tracingHelp :: String
tracingHelp = "Override tracing level (combinations of {" ++ levels ++ "} in quotes, separated by spaces, e.g. " ++ exampleLevels ++ ")"
  where
    levels = render $ vcat theSteps
    exampleLevels = "\"" ++ render (hsep $ map (pretty.fst) namesOfSteps ) ++ "\""
