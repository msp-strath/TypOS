module Main where

import Bwd
import Thin
import Parse
import Actor
import Term
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
  <|> DefnJ <$> pjudge <* punc "@" <*> ((,) <$> pchan <* punc "=" <*> pACT0)
  <|> DeclS <$ plit "syntax" <* punc "{"
       <*> psep (punc ";") ((,) <$> patom <* punc "=" <*> plocal B0 ptm)
       <* pspc <* pch (== '}')
  <|> Go <$ plit "exec" <* pspc <*> pACT0

pfile :: Parser [Command]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

run :: Process Store Bwd -> [Command] -> Process Store []
run p [] = exec p
run p@Process{..} (c : cs) = case c of
  DefnJ jd cha -> run (p { stack = stack :< Rules jd cha }) cs
  Go a -> let (lroot, rroot) = splitRoot root ""
              rbranch = Process [] rroot env () a
          in run (p { stack = stack :< LeftBranch Hole rbranch, root = lroot}) cs
  _ -> run p cs

main :: IO ()
main = do
  args <- getArgs
  let fp = case args of {(fp :_) -> fp; _ -> "stlc.act"}
  txt <- readFile fp
  let cs = parse pfile txt
  putStrLn $ display initNaming $
    run (Process B0 initRoot (initEnv 0) Map.empty Win) cs
