module Command where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Foldable (fold)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Traversable (for)

import qualified Actor as A
import Actor.Display (DAEnv, initDAEnv, declareChannel)
import qualified Concrete.Base as C
import Concrete.Parse
import Bwd
import Display
import Elaboration
import Machine.Base
import Machine.Display (Store)
import Machine.Exec
import Main.Options
import Parse
import Syntax
import Term.Base
import Utils


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
    DeclJ jd p -> do
      st <- get
      forM_ (snd <$> p) $ \ cat -> do
         whenNothing (Map.lookup cat (syntaxCats st)) $
           throwError (DeclJElaboration jd $ NotAValidSyntaxCat cat)
      pure (DeclJ jd p)
    DefnJ (jd, ch) a -> during (DefnJElaboration jd) $ do
      ch <- pure (A.Channel ch)
      resolve jd >>= \case
        Just (Left (AJudgement p)) -> do
          withChannel ch p $ DefnJ (jd, ch) <$> sact a
        Just _ -> throwError (NotAValidJudgement jd)
        _ -> throwError (OutOfScope jd)
    DeclS syns -> do
      oldsyndecls <- gets (Map.keys . syntaxCats)
      let newsyndecls = map fst syns
      syns <- for syns $ \ syn@(cat, _) ->
                during (DeclaringSyntaxCat cat) $ traverse stm syn
      syns0 <- case isAllJustBy syns (traverse isMetaFree) of
                Left a -> throwError (SyntaxContainsMeta (fst a))
                Right syns -> pure syns
      whenLeft (isAll (validateDesc (newsyndecls ++ oldsyndecls) . snd) syns0) $ \ a ->
        throwError (InvalidSyntax (fst a))
      forM_ syns0 (uncurry declareSyntax)
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
