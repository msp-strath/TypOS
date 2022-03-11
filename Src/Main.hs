module Main where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Applicative

import Data.Foldable
import Data.Maybe
import Data.Traversable

import qualified Options.Applicative as Opt

import Bwd
import Elaboration
import Parse
import qualified Actor as A
import Actor.Display (DAEnv, initDAEnv, declareChannel)
import Machine hiding (declareChannel)
import Term
import Display
import Utils

import qualified Concrete.Base as C
import Concrete.Parse

import Syntax

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
         , Display t, DisplayEnv t ~ Naming
         , Display a, DisplayEnv a ~ DAEnv) =>
         Display (CommandF jd ch t a) where
  type DisplayEnv (CommandF jd ch t a) = Naming
  display = \case
    DeclJ jd p -> do
      jd <- subdisplay jd
      p <- subdisplay p
      pure $ unwords [ jd, ":", p]
    d@(DefnJ (jd, ch) a) -> do
      jd <- subdisplay jd
      ch <- subdisplay ch
      -- hack: the above happens to convert ch into a string, ready to be declared
      a <- withEnv (declareChannel (A.Channel ch) initDAEnv) $ display a
      pure $ unwords [ jd, "@", ch, "=", a]
    DeclS s -> do
      s <- traverse (\ (c, t) -> display t >>= \ t -> pure $ unwords ["'" ++ c, "=", t]) s
      pure $ "syntax " ++ collapse (BracesList s)
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
    DeclS syns -> do
      syns <- traverse (traverse stm) syns
      let syndecls = map fst syns
      syns0 <- case isAllJustBy syns (traverse isMetaFree) of
                Left a -> throwError (SyntaxContainsMeta (fst a))
                Right syns -> pure syns
      whenLeft (isAll (validateDesc syndecls . snd) syns0) $ \ a ->
        throwError (InvalidSyntax (fst a))
      pure (DeclS syns)
    Go a -> Go <$> sact a
    Trace ts -> pure (Trace ts)


run :: Options -> Process Store Bwd -> [ACommand] -> Process Store []
run opts p [] = exec p
run opts p@Process{..} (c : cs) = case c of
  DefnJ (jd, ch) a -> run opts (p { stack = stack :< Rules jd (ch, a) }) cs
  Go a -> -- dmesg (show a) $
          let (lroot, rroot) = splitRoot root ""
              rbranch = Process tracing [] rroot env (today store) a ""
          in run opts (p { stack = stack :< LeftBranch Hole rbranch, root = lroot}) cs
  Trace xs -> let tr = fromMaybe (xs ++ tracing) (tracingOption opts)
              in run opts (p { tracing = tr }) cs
  _ -> run opts p cs

data Options = Options
  { filename :: String
  , tracingOption :: Maybe [MachineStep]
  }

options :: Opt.Parser Options
options = Options <$> Opt.argument Opt.str (Opt.metavar "FILE" <> Opt.showDefault <> Opt.value "stlc.act" <> Opt.help "Actor file")
                  <*> (optional $ Opt.option (Opt.str >>= (readSteps . words))
                                             (Opt.long "tracing" <> Opt.metavar "LEVELS" <> Opt.help tracingHelp))
 where
   readSteps :: [String] -> Opt.ReadM [MachineStep]
   readSteps = mapM $ \case
     "recv" -> pure MachineRecv
     "send" -> pure MachineSend
     "exec" -> pure MachineExec
     "move" -> pure MachineMove
     "unify" -> pure MachineUnify
     "break" -> pure MachineBreak
     x -> Opt.readerError $ "Unknown tracing level '" ++ x ++ "'. Accepted levels: " ++ levels
   tracingHelp = "Override tracing level (combinations of {" ++ levels ++ "} in quotes, separated by spaces, e.g. " ++ exampleLevels ++ ")"
   levels = unwords $ map (unsafeEvalDisplay () . display) [(minBound::MachineStep)..]
   exampleLevels = "\"" ++ (unwords $ map (unsafeEvalDisplay () . display) [minBound::MachineStep, maxBound]) ++ "\""

main :: IO ()
main = do
  opts <- Opt.execParser (Opt.info (options <**> Opt.helper)
                         (Opt.fullDesc <> Opt.progDesc "Execute actors in FILE"
                                       <> Opt.header "typOS - an operating system for typechecking processes"))
  txt <- readFile (filename opts)
  let ccs = parse pfile txt
  acs <- case elaborate ccs of
           Left err -> error (show err)
           Right acs -> pure acs
  -- putStrLn $ unsafeEvalDisplay initNaming $ collapse <$> traverse display acs
  let p = Process [] B0 initRoot (A.initEnv B0) initStore A.Win ""
  let res@(Process _ fs _ env sto A.Win _) = run opts p acs
  -- putStrLn $ display initNaming res
  dmesg "" res `seq` pure ()
