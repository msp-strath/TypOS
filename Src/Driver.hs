module Main where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Foldable
import Data.Traversable

import Bwd
import Elaboration
import Thin
import Parse
import qualified Actor as A
-- import Actor.Parse
import Machine
import Term
import Display

import Elaboration

import qualified Concrete.Base as C
import Concrete.Parser

import Syntax

import System.Environment
import Control.Applicative
import qualified Data.Map as Map

data CommandF jd ch t a
  = DeclJ (jd, ch) [(Mode, SyntaxCat)]
  | DefnJ (jd, ch) a
  | DeclS [(SyntaxCat, t)]
  | Go a
  | Trace [MachineStep]
  deriving (Show)

type CCommand = CommandF C.Variable C.Variable C.Raw C.Actor
type ACommand = CommandF A.JudgementForm A.Channel ACTm A.Actor

instance Display Mode where
  display Input = pure "?"
  display Output = pure "!"

instance Display Protocol where
  display p = (fold <$>) $ for p $ \ (m, c) -> do
    m <- display m
    pure $ m ++ c ++ ". "

instance Display String where
  display str = pure str

instance (Display jd, Display ch, Display t, Display a) =>
         Display (CommandF jd ch t a) where
  display = \case
    DeclJ (jd, ch) p -> do
      jd <- display jd
      ch <- display ch
      p <- display p
      pure $ unwords [ jd, "@", ch, ":", p]
    d@(DefnJ (jd, ch) a) -> do
      jd <- display jd
      ch <- display ch
      -- hack: the above happens to convert ch into a string, ready to be declared
      a <- local (declareChannel ch) $ display a
      pure $ unwords [ jd, "@", ch, "=", a]
    DeclS _ -> pure ""
    Go a -> display a
    Trace ts -> pure ""

pmachinestep :: Parser MachineStep
pmachinestep =
  MachineRecv <$ plit "recv"
  <|> MachineSend <$ plit "send"
  <|> MachineExec <$ plit "exec"
  <|> MachineMove <$ plit "move"
  <|> MachineUnify <$ plit "unify"

pmode :: Parser Mode
pmode = Input <$ pch (== '?') <|> Output <$ pch (== '!')

pjudgeat :: Parser (C.Variable, C.Variable)
pjudgeat = (,) <$> pnom <* punc "@" <*> pnom

pprotocol :: Parser Protocol
pprotocol = psep pspc ((,) <$> pmode <* pspc <*> patom <* pspc <* pch (== '.'))

psyntax :: Parser (SyntaxCat, C.Raw)
psyntax = (,) <$> patom <* punc "=" <*> plocal B0 ptm

pcommand :: Parser CCommand
pcommand
    = DeclJ <$> pjudgeat <* punc ":" <*> pprotocol
  <|> DefnJ <$> pjudgeat <* punc "=" <*> pACT
  <|> DeclS <$ plit "syntax" <*> pcurlies (psep (punc ";") psyntax)
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <*> pcurlies (psep (punc ",") pmachinestep)

pfile :: Parser [CCommand]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

collectDecls :: [CCommand] -> Elab Decls
collectDecls [] = asks declarations
collectDecls (DeclJ (jd, ch) p : ccs) = do
  isFresh jd
  local (declare jd (AJudgement (A.Channel ch) p)) $ collectDecls ccs
collectDecls (_ : ccs) = collectDecls ccs

elaborate :: [CCommand] -> Either Complaint [ACommand]
elaborate ccs = evalElab $ do
  ds <- collectDecls ccs
  local (setDecls ds) $ forM ccs $ \case
    DeclJ (jd, ch) p -> pure (DeclJ (jd, A.Channel ch) p)
    DefnJ (jd, ch) a -> do
      ch <- pure (A.Channel ch)
      resolve jd >>= \case
        Just (Left (AJudgement ch' p)) -> do
          when (ch /= ch') $ throwError (MismatchDeclDefn jd ch ch')
          withChannel ch p $ DefnJ (jd, ch) <$> sact a
        Just _ -> throwError (NotAValidJudgement jd)
        _ -> throwError (OutOfScope jd)
    DeclS syns -> DeclS <$> traverse (traverse stm) syns
    Go a -> Go <$> sact a
    Trace ts -> pure (Trace ts)


run :: Process Store Bwd -> [ACommand] -> Process Store []
run p [] = exec p
run p@Process{..} (c : cs) = case c of
  DefnJ (jd, ch) a -> run (p { stack = stack :< Rules jd (ch, a) }) cs
  Go a -> -- dmesg (show a) $
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
  let ccs = parse pfile txt
  acs <- case elaborate ccs of
           Left err -> error (show err)
           Right acs -> pure acs
  -- putStrLn $ unsafeEvalDisplay $ collapse <$> traverse display acs
  let p = Process [] B0 initRoot (A.initEnv 0) initStore A.Win
  let res@(Process _ fs _ env sto A.Win) = run p acs
  -- putStrLn $ display initNaming res
  dmesg "" res `seq` pure ()
