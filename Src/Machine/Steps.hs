{-# LANGUAGE OverloadedStrings #-}
{- | Description: 

-}
module Machine.Steps where

import Pretty (Pretty(pretty))

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

-- | Output 'MachineStep' in a way that's nicer for humans
instance Pretty MachineStep where
  pretty = \case
    MachineRecv -> "recv"
    MachineSend -> "send"
    MachineExec -> "exec"
    MachineMove -> "move"
    MachineUnify -> "unify"
    MachineBreak -> "break"
    MachineClause -> "clause"
