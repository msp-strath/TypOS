module Main where

import Bwd
import Elaboration
import Thin
import Parse
import Actor
import Actor.Parse
import Machine
import Term
import Term.Parse
import Display

import Syntax

import System.Environment
import Control.Applicative
import qualified Data.Map as Map

data Command
  = DeclJ JudgementForm [(Mode, SyntaxCat)]
  | DefnJ JudgementForm (Channel, Actor)
  | DeclS [(SyntaxCat, CdB (Tm String))]
  | Go Actor
  | Trace [MachineStep]
  deriving (Show)

pmachinestep :: Parser MachineStep
pmachinestep =
  MachineRecv <$ plit "recv"
  <|> MachineSend <$ plit "send"
  <|> MachineExec <$ plit "exec"
  <|> MachineMove <$ plit "move"
  <|> MachineUnify <$ plit "unify"

pmode :: Parser Mode
pmode = Input <$ pch (== '?') <|> Output <$ pch (== '!')

pcommand :: Parser Command
pcommand
  = DeclJ <$> pjudge <* punc ":"
     <*> psep pspc ((,) <$> pmode <* pspc <*> patom <* pspc <* pch (== '.'))
  <|> DefnJ <$> pjudge <* punc "@" <*> ((,) <$> pchan <* punc "=" <*> pACT)
  <|> DeclS <$ plit "syntax" <* punc "{"
       <*> psep (punc ";") ((,) <$> patom <* punc "=" <*> plocal B0 ptm)
       <* pspc <* pch (== '}')
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <* pspc <*> psep (punc ",") pmachinestep

pfile :: Parser [Command]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

run :: Process Store Bwd -> [Command] -> Process Store []
run p [] = exec p
run p@Process{..} (c : cs) = case c of
  DefnJ jd cha -> run (p { stack = stack :< Rules jd cha }) cs
  Go a -> dmesg (show a) $
          let (lroot, rroot) = splitRoot root ""
              rbranch = Process tracing [] rroot env (today store) a
          in run (p { stack = stack :< LeftBranch Hole rbranch, root = lroot}) cs
  Trace xs -> run (p { tracing = xs ++ tracing }) cs
  _ -> run p cs

main :: IO ()
main = do
  args <- getArgs
  let fp = case args of {(fp :_) -> fp; _ -> "stlc.act"}
  txt <- readFile fp
  let cs = parse pfile txt
  let p = Process [] B0 initRoot (initEnv 0) initStore Win
  let res@(Process _ fs _ env sto Win) = run p cs
  -- putStrLn $ display initNaming res
  dmesg "" res `seq` pure ()
