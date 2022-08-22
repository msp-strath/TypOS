{-# LANGUAGE UndecidableInstances, OverloadedStrings #-}

module Command where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Bifunctor (first)
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
import Elaboration.Monad
import Elaboration.Pretty()
import Machine.Base
import Machine.Display (Store)
import Machine.Exec
import Machine.Trace (Shots)
import Options
import Parse
import Pretty (keyword, Collapse(..), BracesList(..), Pretty(..))
import Syntax
import Term.Base
import Unelaboration(Unelab(..), subunelab, withEnv, initDAEnv, Naming, declareChannel)
import Location
import Data.Char (isSpace)

type family SYNTAXCAT (ph :: Phase) :: *
type instance SYNTAXCAT Concrete = WithRange SyntaxCat
type instance SYNTAXCAT Abstract = SyntaxCat

type family PROTOCOL (ph :: Phase) :: *
type instance PROTOCOL Concrete = ()
type instance PROTOCOL Abstract = AProtocol

data STATEMENT (ph :: Phase)
  = Statement (JUDGEMENTFORM ph) [Variable]

data COMMAND (ph :: Phase)
  = DeclJudge ExtractMode (JUDGEMENTFORM ph) (Protocol (SYNTAXDESC ph))
  | DefnJudge (JUDGEMENTFORM ph, PROTOCOL ph, CHANNEL ph) (ACTOR ph)
  | ContractJudge [STATEMENT ph] (STATEMENT ph) [STATEMENT ph]
  | DeclSyntax [(SYNTAXCAT ph, SYNTAXDESC ph)]
  | DeclStack (STACK ph) (ContextStack (SYNTAXDESC ph))
  | ContractStack [STATEMENT ph] (STACK ph, Variable, Variable) [STATEMENT ph]
  | Go (ACTOR ph)
  | Trace [MachineStep]

deriving instance
  ( Show (JUDGEMENTFORM ph)
  , Show (CHANNEL ph)
  , Show (BINDER ph)
  , Show (ACTORVAR ph)
  , Show (SCRUTINEEVAR ph)
  , Show (SYNTAXDESC ph)
  , Show (TERMVAR ph)
  , Show (TERM ph)
  , Show (PATTERN ph)
  , Show (CONNECT ph)
  , Show (STACK ph)
  , Show (STACKDESC ph)
  , Show (SYNTAXCAT ph)
  , Show (PROTOCOL ph)
  , Show (LOOKEDUP ph)) =>
  Show (COMMAND ph)

deriving instance
  (Show (JUDGEMENTFORM ph)) =>
  Show (STATEMENT ph)

type CCommand = COMMAND Concrete
type ACommand = COMMAND Abstract
type CStatement = STATEMENT Concrete
type AStatement = STATEMENT Abstract

instance Display Mode where
  type DisplayEnv Mode = ()
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display (ContextStack t) where
  type DisplayEnv (ContextStack t) = UnelabEnv t
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display (Protocol t) where
  type DisplayEnv (Protocol t) = UnelabEnv t
  display = viaPretty

instance Pretty CStatement where
  pretty (Statement jd vars) = hsep $ pretty jd : (pretty <$> vars)

instance Pretty CCommand where
  pretty = let prettyCds cds = collapse (BracesList $ pretty <$> cds) in \case
    DeclJudge em jd p -> hsep [pretty em <> pretty jd, colon, pretty p]
    DefnJudge (jd, _, ch) a -> hsep [pretty jd <> "@" <> pretty ch, equal, pretty a]
    ContractJudge pres stm posts -> hsep [prettyCds pres, pretty stm, prettyCds posts]
    DeclSyntax s -> let docs = fmap (\ (cat, desc) -> pretty (theValue cat) <+> equal <+> pretty desc) s in
               keyword "syntax" <+> collapse (BracesList docs)
    DeclStack stk stkTy -> hsep [pretty stk, "|-", pretty stkTy]
    ContractStack pres (stk, lhs, rhs) posts -> hsep [prettyCds pres
                                                     , pretty stk, pretty lhs, "=", pretty rhs
                                                     , prettyCds posts]
    Go a -> keyword "exec" <+> pretty a
    Trace ts -> keyword "trace" <+> collapse (BracesList $ map pretty ts)


instance Unelab ACommand where
  type UnelabEnv ACommand = Naming
  type Unelabed ACommand = CCommand
  unelab = \case
    DeclJudge em jd a -> DeclJudge em <$> subunelab jd <*> unelab a
    DefnJudge (jd, _, ch) a -> DefnJudge <$> ((,,) <$> subunelab jd <*> pure () <*> subunelab ch)
                              <*> withEnv (declareChannel ch initDAEnv) (unelab a)
    ContractJudge pres stm posts -> ContractJudge <$> traverse subunelab pres <*> subunelab stm
                                    <*> traverse subunelab posts
    DeclSyntax s -> DeclSyntax . map (first (WithRange unknown)) <$> traverse (traverse unelab) s
    DeclStack stk stkTy -> DeclStack <$> subunelab stk <*> traverse unelab stkTy
    ContractStack pres (stk, lhs, rhs) posts -> ContractStack <$> traverse subunelab pres
                                                <*> fmap (, lhs, rhs) (subunelab stk)
                                                <*> traverse subunelab posts
    Go a -> Go <$> withEnv initDAEnv (unelab a)
    Trace ts -> pure $ Trace ts

instance Unelab AStatement where
  type UnelabEnv AStatement = ()
  type Unelabed AStatement = CStatement
  unelab (Statement jd vars) = (`Statement` vars) <$> unelab jd

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

psyntax :: Parser (WithRange SyntaxCat, Raw)
psyntax = (,) <$> withRange (WithRange unknown <$> patom) <* punc "=" <*> psyntaxdecl

pstatement :: Parser CStatement
pstatement = Statement <$> pvariable <*> many (id <$ pspc <*> pvariable)

pconditions :: Parser [CStatement]
pconditions = pcurlies (psep (punc ",") pstatement)

pcommand :: Parser CCommand
pcommand
    = DeclJudge <$> pextractmode <*> pvariable <* punc ":" <*> pprotocol
  <|> DefnJudge <$> pjudgeat <* punc "=" <*> pACT
  <|> ContractJudge <$> pconditions <* pspc <*> pstatement <* pspc <*> pconditions
  <|> DeclSyntax <$ plit "syntax" <*> pcurlies (psep (punc ";") psyntax)
  <|> DeclStack <$> pvariable <* punc "|-" <*> pcontextstack
  <|> ContractStack <$> pconditions <* pspc
                    <*> ((,,) <$> pvariable <* punc "|-" <*> pvariable <* punc "->" <*> pvariable)
                    <* pspc <*> pconditions
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <*> pcurlies (psep (punc ",") pmachinestep)

pfile :: Parser [CCommand]
pfile = id <$ pspc <*> psep pspc pcommand <* pspc

pmarkdown :: Parser [CCommand]
pmarkdown = concat <$ pmdspc <*> psep pmdspc (id <$> pfile <* pspc <* plit "```") <* pmdspc

  where

  toBlock :: String -> Location -> Source
  toBlock str loc =
    let (ign, rest) = span (/= '`') str in
    let loc' = ticks loc ign in
    case rest of
      '`':'`':'`':rest -> insideBlock rest (ticks loc' "```")
      c:rest -> toBlock rest (Location.tick loc' c)
      [] -> Source [] loc'

  insideBlock :: String -> Location -> Source
  insideBlock str loc =
    let (decl, rest) = span (/= '\n') str in
    let loc' = ticks loc decl in
    case decl of
      ds | all isSpace ds -> Source rest loc'
      't':'y':'p':'o':'s':ds | all isSpace ds -> Source rest loc'
      _ -> exitBlock rest loc'

  exitBlock :: String -> Location -> Source
  exitBlock str loc =
    let (ign, rest) = span (/= '`') str in
    let loc' = ticks loc ign in
    case rest of
      '`':'`':'`':rest -> toBlock rest (ticks loc' "```")
      c:rest -> exitBlock rest (Location.tick loc' c)
      [] -> parseError Precise loc "Couldn't find end of fenced code block."

  pmdspc :: Parser ()
  pmdspc = Parser $ \ (Source str loc) -> here ((), toBlock str loc)

scondition :: CStatement -> Elab AStatement
scondition (Statement jd vars) = do
 jd <- judgementName <$> isJudgement jd
 -- TODO: additional checks for `vars`, maybe?
 pure $ Statement jd vars

scommand :: CCommand -> Elab (ACommand, Decls)
scommand = \case
  DeclJudge em jd p -> during (DeclJElaboration jd) $ do
    jd <- isFresh jd
    p <- sprotocol p
    local (declare (Used jd) (AJudgement em p)) $
      (DeclJudge em jd p,) <$> asks declarations
  DefnJudge (jd, (), ch) a -> during (DefnJElaboration jd) $ do
    let rp = getRange jd <> getRange ch
    ch <- Channel <$> isFresh ch
    jd <- isJudgement jd
    a <- withChannel rp Rootwards ch (judgementProtocol jd) $ local (setElabMode Definition) (sact a)
    (DefnJudge (judgementName jd, judgementProtocol jd, ch) a,) <$> asks declarations
  ContractJudge pres stm posts -> do
    pres  <- traverse scondition pres
    stm   <- scondition stm
    posts <- traverse scondition posts
    -- TODO : additional checks
    (ContractJudge pres stm posts,) <$> asks declarations
  DeclSyntax syns -> do
    oldsyndecls <- gets (Map.keys . syntaxCats)
    let newsyndecls = map (theValue . fst) syns
    let syndecls = newsyndecls ++ oldsyndecls
    syns <- for syns $ \ syn@(cat, _) ->
              during (DeclaringSyntaxCat (theValue cat)) $
                traverse (ssyntaxdecl syndecls) syn
    forM_ syns (uncurry declareSyntax)
    (DeclSyntax (map (first theValue) syns),) <$> asks declarations
  DeclStack stk stkTy -> do
    stk <- isFresh stk
    stkTy <- scontextstack stkTy
    local (declare (Used stk) (AStack stkTy)) $ do
      (DeclStack (Stack stk) stkTy,) <$> asks declarations
  ContractStack pres (stk, lhs, rhs) posts -> do
    pres  <- traverse scondition pres
    (stk,_) <- isContextStack stk
    posts <- traverse scondition posts
    -- TODO : additional checks for `lhs`, `rhs`
    (ContractStack pres (stk, lhs, rhs) posts,) <$> asks declarations
  Go a -> during ExecElaboration $ (,) . Go <$> local (setElabMode Execution) (sact a) <*> asks declarations
  Trace ts -> (Trace ts,) <$> asks declarations

scommands :: [CCommand] -> Elab [ACommand]
scommands [] = pure []
scommands (c:cs) = do
  (c, ds) <- scommand c
  cs <- local (setDecls ds) $ scommands cs
  pure (c:cs)

elaborate :: [CCommand] -> Either Complaint ([Warning], [ACommand], SyntaxTable)
elaborate ccs = evalElab $ do
  acs <- scommands ccs
  st <- get
  pure (warnings st <>> [], acs, syntaxCats st)

run :: Options -> Process Shots Store Bwd -> [ACommand] -> Process Shots Store []
run opts p [] = exec p
run opts p@Process{..} (c : cs) = case c of
  DeclJudge em jd _ -> run opts p cs
  DefnJudge (jd, jdp, ch) a -> run opts (p { stack = stack :< Rules jd jdp (ch, a) }) cs
  Go a -> -- dmesg (show a) $
          let (lroot, rroot) = splitRoot root ""
              rbranch = Process opts [] rroot env New a ()
          in run opts (p { stack = stack :< LeftBranch Hole rbranch, root = lroot}) cs
  Trace xs -> let trac = guard (not $ quiet opts) >> fromMaybe (xs ++ tracing p) (tracingOption opts)
                  newOpts = opts { tracingOption = Just trac }
              in run newOpts (p { options = newOpts }) cs
  _ -> run opts p cs
