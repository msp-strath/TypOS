{-# LANGUAGE UndecidableInstances, OverloadedStrings #-}

module Command where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Traversable (for)

import Actor
import Actor.Display ()

import Concrete.Base
import Concrete.Parse
import Concrete.Pretty()
import Bwd
import Display(Display(..), viaPretty)
import Doc
import Elaboration
import Elaboration.Pretty()
import Machine.Base
import Machine.Display (Store)
import Machine.Exec
import Options
import Parse
import Pretty (keyword, Collapse(..), BracesList(..), Pretty(..))
import Syntax
import Term.Base
import Unelaboration(Unelab(..), subunelab, withEnv, initDAEnv, Naming, declareChannel)

data CommandF jd ch syn a
  = DeclJ jd (Maybe (JudgementStack syn)) (Protocol syn)
  | DefnJ (jd, ch) a
  | DeclS [(SyntaxCat, syn)]
  | Go a
  | Trace [MachineStep]
  deriving (Show)

type CCommand = CommandF Variable Variable Raw CActor
type ACommand = CommandF JudgementForm Channel SyntaxDesc AActor

instance Display Mode where
  type DisplayEnv Mode = ()
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display (JudgementStack t) where
  type DisplayEnv (JudgementStack t) = UnelabEnv t
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display (Protocol t) where
  type DisplayEnv (Protocol t) = UnelabEnv t
  display = viaPretty

instance Pretty CCommand where
  pretty = \case
    DeclJ jd mstk p -> pretty jd <> maybe "" (\ stk -> space <> pretty stk <+> "|-") mstk <+> pretty p
    DefnJ (jd, ch) a -> hsep [pretty jd <> "@" <> pretty ch, equal, pretty a]
    DeclS s -> let docs = fmap (\ (cat, desc) -> pretty cat <+> equal <+> pretty desc) s in
               keyword "syntax" <+> collapse (BracesList docs)
    Go a -> keyword "exec" <+> pretty a
    Trace ts -> keyword "trace" <+> collapse (BracesList $ map pretty ts)

instance Unelab ACommand where
  type UnelabEnv ACommand = Naming
  type Unelabed ACommand = CCommand
  unelab = \case
    DeclJ jd mstk p -> DeclJ <$> subunelab jd <*> traverse unelab mstk <*> unelab p
    DefnJ (jd, ch) a -> DefnJ <$> ((,) <$> subunelab jd <*> subunelab ch)
                              <*> withEnv (declareChannel ch initDAEnv) (unelab a)
    DeclS s -> DeclS <$> traverse (traverse unelab) s
    Go a -> Go <$> withEnv initDAEnv (unelab a)
    Trace ts -> pure $ Trace ts

instance Display ACommand where
  type DisplayEnv ACommand = Naming
  display = viaPretty

pmachinestep :: Parser MachineStep
pmachinestep =
  MachineRecv <$ plit "recv"
  <|> MachineSend <$ plit "send"
  <|> MachineExec <$ plit "exec"
  <|> MachineMove <$ plit "move"
  <|> MachineUnify <$ plit "unify"
  <|> MachineBreak <$ plit "break"

pjudgeat :: Parser (Variable, Variable)
pjudgeat = (,) <$> pvariable <* punc "@" <*> pvariable

psyntax :: Parser (SyntaxCat, Raw)
psyntax = (,) <$> patom <* punc "=" <*> psyntaxdecl

pcommand :: Parser CCommand
pcommand
    = DeclJ <$> pvariable <* punc ":" <*> poptional pjudgementstack <*> pprotocol
  <|> DefnJ <$> pjudgeat <* punc "=" <*> pACT
  <|> DeclS <$ plit "syntax" <*> pcurlies (psep (punc ";") psyntax)
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <*> pcurlies (psep (punc ",") pmachinestep)

pfile :: Parser [CCommand]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

scommand :: CCommand -> Elab (ACommand, Decls)
scommand = \case
  DeclJ jd mstk p -> during (DeclJElaboration jd) $ do
    jd <- isFresh jd
    mstk <- traverse sjudgementstack mstk
    p <- sprotocol p
    local (declare jd (AJudgement mstk p)) $
      (DeclJ jd mstk p,) <$> asks declarations
  DefnJ (jd, ch) a -> during (DefnJElaboration jd) $ do
    ch <- Channel <$> isFresh ch
    (jd, mstk, p) <- isJudgement jd
    local (setCurrentActor jd mstk) $ do
      a <- withChannel ch p $ sact a
      (DefnJ (jd, ch) a,) <$> asks declarations
  DeclS syns -> do
    oldsyndecls <- gets (Map.keys . syntaxCats)
    let newsyndecls = map fst syns
    let syndecls = newsyndecls ++ oldsyndecls
    syns <- for syns $ \ syn@(cat, _) ->
              during (DeclaringSyntaxCat cat) $
                traverse (ssyntaxdecl syndecls) syn
    forM_ syns (uncurry declareSyntax)
    (DeclS syns,) <$> asks declarations
  Go a -> during ExecElaboration $ (,) . Go <$> sact a <*> asks declarations
  Trace ts -> (Trace ts,) <$> asks declarations

scommands :: [CCommand] -> Elab [ACommand]
scommands [] = pure []
scommands (c:cs) = do
  (c, ds) <- scommand c
  cs <- local (setDecls ds) $ scommands cs
  pure (c:cs)

elaborate :: [CCommand] -> Either Complaint [ACommand]
elaborate = evalElab . scommands

run :: Options -> Process Store Bwd -> [ACommand] -> Process Store []
run opts p [] = exec p
run opts p@Process{..} (c : cs) = case c of
  DefnJ (jd, ch) a -> run opts (p { stack = stack :< Rules jd (ch, a) }) cs
  Go a -> -- dmesg (show a) $
          let (lroot, rroot) = splitRoot root ""
              rbranch = Process tracing [] rroot env (today store) a ""
          in run opts (p { stack = stack :< LeftBranch Hole rbranch, root = lroot}) cs
  Trace xs -> let tr = guard (not $ quiet opts) >> fromMaybe (xs ++ tracing) (tracingOption opts)
              in run opts (p { tracing = tr }) cs
  _ -> run opts p cs
