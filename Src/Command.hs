module Command where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Traversable (for)

import qualified Actor as A
import Actor.Display (DAEnv, initDAEnv, declareChannel)
import Concrete.Base (Variable(..))
import qualified Concrete.Base as C
import Concrete.Parse
import Bwd
import Display
import Elaboration
import Elaboration.Pretty()
import Machine.Base
import Machine.Display (Store)
import Machine.Exec
import Main.Options
import Parse
import Pretty
import Syntax
import Term.Base

data CommandF jd ch syn a
  = DeclJ jd (Maybe (JudgementStack syn)) (Protocol syn)
  | DefnJ (jd, ch) a
  | DeclS [(SyntaxCat, syn)]
  | Go a
  | Trace [MachineStep]
  deriving (Show)

type CCommand = CommandF C.Variable C.Variable C.Raw C.Actor
type ACommand = CommandF A.JudgementForm A.Channel SyntaxDesc A.Actor

instance Display Mode where
  type DisplayEnv Mode = ()
  display = pure . pretty

instance Display t => Display (JudgementStack t) where
  type DisplayEnv (JudgementStack t) = DisplayEnv t
  display stk = do
    key <- display (keyDesc stk)
    desc <- display (valueDesc stk)
    pure $ unwords [key , "->", desc ]

instance Display t => Display (Protocol t) where
  type DisplayEnv (Protocol t) = DisplayEnv t
  display t = do
    t <- traverse (traverse display) t
    pure (pretty t)

instance Display String where
  type DisplayEnv String = ()
  display str = pure str

instance ( Display0 jd, Display0 ch
         , Display syn, DisplayEnv syn ~ ()
         , Display a, DisplayEnv a ~ DAEnv) =>
         Display (CommandF jd ch syn a) where
  type DisplayEnv (CommandF jd ch syn a) = Naming
  display = \case
    DeclJ jd stk p -> do
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
      s <- traverse (\ (c, t) -> subdisplay t >>= \ t -> pure $ unwords ["'" ++ c, "=", t]) s
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
pjudgeat = (,) <$> pvariable <* punc "@" <*> pvariable

pprotocol :: Parser (Protocol C.Raw)
pprotocol = psep pspc ((,) <$> pmode <* pspc <*> psyntaxdecl <* pspc <* pch (== '.'))

psyntax :: Parser (SyntaxCat, C.Raw)
psyntax = (,) <$> patom <* punc "=" <*> psyntaxdecl

psyntaxdecl :: Parser C.Raw
psyntaxdecl = plocal B0 ptm

pjudgementstack :: Parser (JudgementStack C.Raw)
pjudgementstack =
   JudgementStack <$> psyntaxdecl <* punc "->" <*> psyntaxdecl <* punc "|-"

pcommand :: Parser CCommand
pcommand
    = DeclJ <$> pvariable <* punc ":" <*> poptional pjudgementstack <*> pprotocol
  <|> DefnJ <$> pjudgeat <* punc "=" <*> pACT
  <|> DeclS <$ plit "syntax" <*> pcurlies (psep (punc ";") psyntax)
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <*> pcurlies (psep (punc ",") pmachinestep)

pfile :: Parser [CCommand]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

sprotocol :: CProtocol -> Elab AProtocol
sprotocol ps = during (ProtocolElaboration ps) $ do
  syndecls <- gets (Map.keys . syntaxCats)
  traverse (traverse (ssyntaxdecl syndecls)) ps

ssyntaxdecl :: [SyntaxCat] -> C.Raw -> Elab SyntaxDesc
ssyntaxdecl syndecls syn = do
  let desc = catToDesc "Syntax"
  syn <- withSyntax (syntaxDesc syndecls) $ stm desc syn
  case isMetaFree syn of
    Nothing -> throwError undefined -- this should be impossible, since parsed in empty context
    Just syn0 -> pure syn0

sjudgementstack :: JudgementStack C.Raw -> Elab (JudgementStack SyntaxDesc)
sjudgementstack (JudgementStack key val) = do
  syndecls <- gets (Map.keys . syntaxCats)
  key <- ssyntaxdecl syndecls key
  val <- ssyntaxdecl syndecls val
  pure (JudgementStack key val)

scommand :: CCommand -> Elab (ACommand, Decls)
scommand = \case
  DeclJ jd mstk p -> during (DeclJElaboration jd) $ do
    jd <- isFresh jd
    mstk <- traverse sjudgementstack mstk
    p <- sprotocol p
    local (declare jd (AJudgement mstk p)) $
      (DeclJ jd mstk p,) <$> asks declarations
  DefnJ (jd, ch) a -> during (DefnJElaboration jd) $ do
    ch <- A.Channel <$> isFresh ch
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
  Go a -> (,) . Go <$> sact a <*> asks declarations
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
  Trace xs -> let tr = fromMaybe (xs ++ tracing) (tracingOption opts)
              in run opts (p { tracing = tr }) cs
  _ -> run opts p cs
