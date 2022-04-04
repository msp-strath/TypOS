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
import Machine.Trace (Tracing(..))
import Options
import Parse
import Pretty (keyword, Collapse(..), BracesList(..), Pretty(..))
import Syntax
import Term.Base
import Unelaboration(Unelab(..), subunelab, withEnv, initDAEnv, Naming, declareChannel)

data ExtractMode = AlwaysExtract | TopLevelExtract | InterestingExtract
  deriving (Show)

data CommandF jd p ch syn a
  = DeclJ ExtractMode jd (Maybe (JudgementStack syn)) (Protocol syn)
  | DefnJ (jd, p, ch) a
  | DeclS [(SyntaxCat, syn)]
  | Go a
  | Trace [MachineStep]
  deriving (Show)

type CCommand = CommandF Variable () Variable Raw CActor
type ACommand = CommandF JudgementForm AProtocol Channel SyntaxDesc AActor

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

instance Pretty ExtractMode where
  pretty = \case
    AlwaysExtract -> ""
    TopLevelExtract -> "/"
    InterestingExtract -> "^"

instance Pretty CCommand where
  pretty = \case
    DeclJ em jd mstk p -> pretty em <> pretty jd <> maybe "" (\ stk -> space <> pretty stk <+> "|-") mstk <+> pretty p
    DefnJ (jd, _, ch) a -> hsep [pretty jd <> "@" <> pretty ch, equal, pretty a]
    DeclS s -> let docs = fmap (\ (cat, desc) -> pretty cat <+> equal <+> pretty desc) s in
               keyword "syntax" <+> collapse (BracesList docs)
    Go a -> keyword "exec" <+> pretty a
    Trace ts -> keyword "trace" <+> collapse (BracesList $ map pretty ts)

instance Unelab ACommand where
  type UnelabEnv ACommand = Naming
  type Unelabed ACommand = CCommand
  unelab = \case
    DeclJ em jd mstk a -> DeclJ em <$> subunelab jd <*> traverse unelab mstk <*> unelab a
    DefnJ (jd, _, ch) a -> DefnJ <$> ((,,) <$> subunelab jd <*> pure () <*> subunelab ch)
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

pjudgeat :: Parser (Variable, (), Variable)
pjudgeat = (,,) <$> pvariable <*> punc "@" <*> pvariable

psyntax :: Parser (SyntaxCat, Raw)
psyntax = (,) <$> patom <* punc "=" <*> psyntaxdecl

pextractmode :: Parser ExtractMode
pextractmode
    = TopLevelExtract <$ plit "/" <* pspc
  <|> InterestingExtract <$ plit "^" <* pspc
  <|> pure AlwaysExtract

pcommand :: Parser CCommand
pcommand
    = DeclJ <$> pextractmode <*> pvariable <* punc ":" <*> poptional pjudgementstack <*> pprotocol
  <|> DefnJ <$> pjudgeat <* punc "=" <*> pACT
  <|> DeclS <$ plit "syntax" <*> pcurlies (psep (punc ";") psyntax)
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <*> pcurlies (psep (punc ",") pmachinestep)

pfile :: Parser [CCommand]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

scommand :: CCommand -> Elab (ACommand, Decls)
scommand = \case
  DeclJ em jd mstk p -> during (DeclJElaboration jd) $ do
    jd <- isFresh jd
    mstk <- traverse sjudgementstack mstk
    p <- sprotocol p
    local (declare jd (AJudgement mstk p)) $
      (DeclJ em jd mstk p,) <$> asks declarations
  DefnJ (jd, (), ch) a -> during (DefnJElaboration jd) $ do
    ch <- Channel <$> isFresh ch
    (jd, mstk, p) <- isJudgement jd
    local (setCurrentActor jd mstk) $ do
      a <- withChannel ch p $ sact a
      (DefnJ (jd, p, ch) a,) <$> asks declarations
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

updateTracing :: ExtractMode -> JudgementForm -> Tracing -> Tracing
updateTracing AlwaysExtract jd tr = tr
updateTracing TopLevelExtract jd tr = tr { topLevel = jd : topLevel tr }
updateTracing InterestingExtract jd tr = tr { interesting = jd : interesting tr }

run :: Options -> Tracing -> Process Store Bwd -> [ACommand] -> (Tracing, Process Store [])
run opts tr p [] = (tr, exec p)
run opts tr p@Process{..} (c : cs) = case c of
  DeclJ em jd _ _ -> run opts (updateTracing em jd tr) p cs
  DefnJ (jd, jdp, ch) a -> run opts tr (p { stack = stack :< Rules jd jdp (ch, a) }) cs
  Go a -> -- dmesg (show a) $
          let (lroot, rroot) = splitRoot root ""
              rbranch = Process tracing [] rroot env New a ""
          in run opts tr (p { stack = stack :< LeftBranch Hole rbranch, root = lroot}) cs
  Trace xs -> let trac = guard (not $ quiet opts) >> fromMaybe (xs ++ tracing) (tracingOption opts)
              in run opts tr (p { tracing = trac }) cs
  _ -> run opts tr p cs
