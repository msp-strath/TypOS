module Main where

import Control.Monad.Except
import Control.Monad.Reader

import Data.Foldable
import Data.Traversable

import Bwd
import Elaboration
import Parse
import qualified Actor as A
import Actor.Display (DAEnv, initDAEnv, declareChannel)
import Machine hiding (declareChannel)
import Term
import Display


import qualified Concrete.Base as C
import Concrete.Parse

import Syntax

import System.Environment
import Control.Applicative

data CommandF jd ch t a
  = DeclJ jd [(Mode, SyntaxCat)]
  | DefnJ (jd, ch) a
  | DeclS [(SyntaxCat, t)]
  | Go a
  | Trace [MachineStep]
  deriving (Show)

type CCommand = CommandF C.Variable C.Variable C.Raw C.Actor
type ACommand = CommandF A.JudgementForm A.Channel ACTm A.Actor

instance Display Mode where
  type DisplayEnv Mode = ()
  display Input = pure "?"
  display Output = pure "!"

instance Display Protocol where
  type DisplayEnv Protocol = ()
  display p = (fold <$>) $ for p $ \ (m, c) -> do
    m <- display m
    pure $ m ++ c ++ ". "

instance Display String where
  type DisplayEnv String = ()
  display str = pure str

instance ( Display0 jd, Display0 ch
         , Show t -- , Display t, Forget Naming (DisplayEnv t)
         , Display a, DisplayEnv a ~ DAEnv) =>
         Display (CommandF jd ch t a) where
  type DisplayEnv (CommandF jd ch t a) = ()
  display = \case
    DeclJ jd p -> do
      jd <- display jd
      p <- display p
      pure $ unwords [ jd, ":", p]
    d@(DefnJ (jd, ch) a) -> do
      jd <- display jd
      ch <- display ch
      -- hack: the above happens to convert ch into a string, ready to be declared
      a <- withEnv (declareChannel (A.Channel ch) initDAEnv) $ display a
      pure $ unwords [ jd, "@", ch, "=", a]
    DeclS _ -> pure ""
    Go a -> withEnv initDAEnv $ display a
    Trace ts -> pure ""

pmachinestep :: Parser MachineStep
pmachinestep =
  MachineRecv <$ plit "recv"
  <|> MachineSend <$ plit "send"
  <|> MachineExec <$ plit "exec"
  <|> MachineMove <$ plit "move"
  <|> MachineUnify <$ plit "unify"
  <|> MachineBreak <$ plit "break"

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
    = DeclJ <$> pnom <* punc ":" <*> pprotocol
  <|> DefnJ <$> pjudgeat <* punc "=" <*> pACT
  <|> DeclS <$ plit "syntax" <*> pcurlies (psep (punc ";") psyntax)
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <*> pcurlies (psep (punc ",") pmachinestep)

pfile :: Parser [CCommand]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

collectDecls :: [CCommand] -> Elab Decls
collectDecls [] = asks declarations
collectDecls (DeclJ jd p : ccs) = do
  during (DeclJElaboration jd) $ isFresh jd
  local (declare jd (AJudgement p)) $ collectDecls ccs
collectDecls (_ : ccs) = collectDecls ccs

elaborate :: [CCommand] -> Either Complaint [ACommand]
elaborate ccs = evalElab $ do
  ds <- collectDecls ccs
  local (setDecls ds) $ forM ccs $ \case
    DeclJ jd p -> pure (DeclJ jd p)
    DefnJ (jd, ch) a -> during (DefnJElaboration jd) $ do
      ch <- pure (A.Channel ch)
      resolve jd >>= \case
        Just (Left (AJudgement p)) -> do
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
              rbranch = Process tracing [] rroot env (today store) a ""
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
  let p = Process [] B0 initRoot (A.initEnv B0) initStore A.Win ""
  let res@(Process _ fs _ env sto A.Win _) = run p acs
  -- putStrLn $ display initNaming res
  dmesg "" res `seq` pure ()
