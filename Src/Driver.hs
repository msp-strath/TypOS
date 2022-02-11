module Main where

import Bwd
import Thin
import Parse
import Actor
import Actor.Parse
import Machine
import Term
import Term.Parse
import Display

import System.Environment
import Control.Applicative
import qualified Data.Map as Map


data Mode = Input | {- Subject | -} Output
  deriving (Show)

type Category = String

data Command
  = DeclJ JudgementForm [(Mode, Category)]
  | DefnJ JudgementForm (Channel, Actor)
  | DeclS [(Category, CdB (Tm String))]
  | Go Actor
  deriving (Show)

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

pfile :: Parser [Command]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

run :: Process Store Bwd -> [Command] -> Process Store []
run p [] = exec p
run p@Process{..} (c : cs) = case c of
  DefnJ jd cha -> run (p { stack = stack :< Rules jd cha }) cs
  Go a -> dmesg (show a) $
          let (lroot, rroot) = splitRoot root ""
              rbranch = Process [] rroot env (today store) a
          in run (p { stack = stack :< LeftBranch Hole rbranch, root = lroot}) cs
  _ -> run p cs

main :: IO ()
main = do
  args <- getArgs
  let fp = case args of {(fp :_) -> fp; _ -> "stlc.act"}
  txt <- readFile fp
  let cs = parse pfile txt
  let p = Process B0 initRoot (initEnv 0) initStore Win
  let res@(Process fs _ env sto Win) = run p cs
  -- putStrLn $ display initNaming res
  dmesg "" res `seq` pure ()
