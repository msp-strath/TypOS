{-# LANGUAGE UndecidableInstances, OverloadedStrings #-}

module Command where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Bifunctor (bimap, first)
import Data.Function (on)
import Data.List (sort, sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, catMaybes)
import Data.Traversable (for)
import Data.These
import Data.Either
import Data.Foldable (fold)

import Actor
import Actor.Display ()

import Concrete.Base
import Concrete.Parse
import Concrete.Pretty()
import Bwd
import Display(Display(..), viaPretty)
import Elaboration
import Elaboration.Monad
import Elaboration.Pretty()
import Machine.Base
import Machine.Display (Store)
import Machine.Exec
import Machine.Trace (Shots)
import Options
import Parse
import Pretty
import Rules
import Syntax
import Term.Base
import Unelaboration(Unelab(..), subunelab, withEnv, initDAEnv, Naming, declareChannel)
import Location
import Utils

import Data.Char (isSpace)
import qualified Data.Set as Set
import Operator

type family SYNTAXCAT (ph :: Phase) :: *
type instance SYNTAXCAT Concrete = WithRange SyntaxCat
type instance SYNTAXCAT Abstract = SyntaxCat

type family DEFNPROTOCOL (ph :: Phase) :: *
type instance DEFNPROTOCOL Concrete = ()
type instance DEFNPROTOCOL Abstract = AProtocol

data STATEMENT (ph :: Phase)
  = Statement (JUDGEMENTNAME ph) [Variable]

data COMMAND (ph :: Phase)
  = DeclJudge ExtractMode (JUDGEMENTNAME ph) (PROTOCOL ph)
  | DefnJudge (JUDGEMENTNAME ph, DEFNPROTOCOL ph, CHANNEL ph) (ACTOR ph)
  | ContractJudge [STATEMENT ph] (STATEMENT ph) [STATEMENT ph]
  | DeclSyntax [(SYNTAXCAT ph, SYNTAXDESC ph)]
  | DeclStack (STACK ph) (ContextStack (SYNTAXDESC ph))
  | ContractStack [STATEMENT ph] (STACK ph, Variable, Variable) [STATEMENT ph]
  | Go (ACTOR ph)
  | Trace [MachineStep]
  | DeclOp [ANOPERATOR ph]
  | DefnOp (DEFNOP ph)
  | DeclJudgementForm (JUDGEMENTFORM ph)
  | DeclRule (RULE ph)


deriving instance
  ( Show (JUDGEMENTNAME ph)
  , Show (CHANNEL ph)
  , Show (BINDER ph)
  , Show (ACTORVAR ph)
  , Show (SCRUTINEEVAR ph)
  , Show (SCRUTINEETERM ph)
  , Show (SYNTAXDESC ph)
  , Show (TERMVAR ph)
  , Show (TERM ph)
  , Show (PATTERN ph)
  , Show (CONNECT ph)
  , Show (STACK ph)
  , Show (STACKDESC ph)
  , Show (SYNTAXCAT ph)
  , Show (OPERATOR ph)
  , Show (PROTOCOL ph)
  , Show (DEFNPROTOCOL ph)
  , Show (LOOKEDUP ph)
  , Show (DEFNOP ph)
  , Show (JUDGEMENTFORM ph)
  , Show (RULE ph)
  , Show (GUARD ph)) =>
  Show (COMMAND ph)

deriving instance
  (Show (JUDGEMENTNAME ph)) =>
  Show (STATEMENT ph)

type CCommand = COMMAND Concrete
type ACommand = COMMAND Abstract
type CStatement = STATEMENT Concrete
type AStatement = STATEMENT Abstract

instance (Show a, Unelab a, Pretty (Unelabed a)) => Display (Mode a) where
  type DisplayEnv (Mode a) = UnelabEnv a
  display = viaPretty

instance (Show t, Unelab t, Pretty (Unelabed t)) =>
  Display (ContextStack t) where
  type DisplayEnv (ContextStack t) = UnelabEnv t
  display = viaPretty

instance Display AProtocol where
  type DisplayEnv AProtocol = Naming
  display = viaPretty

instance Pretty CStatement where
  pretty (Statement jd vars) = hsep $ pretty jd : (pretty <$> vars)

instance Pretty (PLACE Concrete) where
  pretty (v, CitizenPlace) = pretty v
  pretty (v, SubjectPlace syntaxdesc semanticsdesc) =
    parens $ hsep $ [ pretty v, ":", pretty syntaxdesc ]
      ++ (("=>" <+> pretty semanticsdesc) <$ guard (syntaxdesc /= semanticsdesc))

instance Pretty CCommand where
  pretty = let prettyCds cds = collapse (BracesList $ pretty <$> cds) in \case
    DeclJudge em jd p -> hsep [pretty em <> pretty jd, colon, pretty p]
    DefnJudge (jd, _, ch) a -> hsep [pretty jd <> "@" <> pretty ch, equals, pretty a]
    ContractJudge pres stm posts -> hsep [prettyCds pres, pretty stm, prettyCds posts]
    DeclSyntax s -> let docs = fmap (\ (cat, desc) -> pretty (theValue cat) <+> equals <+> pretty desc) s in
               keyword "syntax" <+> collapse (BracesList docs)
    DeclStack stk stkTy -> hsep [pretty stk, "|-", pretty stkTy]
    ContractStack pres (stk, lhs, rhs) posts -> hsep [prettyCds pres
                                                     , pretty stk, pretty lhs, "=", pretty rhs
                                                     , prettyCds posts]
    Go a -> keyword "exec" <+> pretty a
    Trace ts -> keyword "trace" <+> collapse (BracesList $ map pretty ts)
    -- DeclJudgementForm j -> keyword "judgementform" <+> collapse (BracesList $ pretty <$> jpreconds j)
    --                    <+> hsep (pretty (jname j) : map pretty (jplaces j))
    --                    <+> collapse (BracesList $ either pretty pretty <$> jpostconds j)

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
psyntax = (,) <$> pwithRange patom <* punc "=" <*> psyntaxdecl

pstatement :: Parser CStatement
pstatement = Statement <$> pvariable <*> many (id <$ pspc <*> pvariable)

pconditions :: Parser [CStatement]
pconditions = pcurlies (psep (punc ",") pstatement)

pcommand :: Parser CCommand
pcommand
    = DeclJudge <$> pextractmode <*> pvariable <* punc ":" <*> pprotocol
  <|> DefnJudge <$> pjudgeat <* punc "=" <*> pACT
  <|> ContractJudge <$> pconditions <* pspc <*> pstatement <* pspc <*> pconditions
  <|> DeclSyntax <$ plit "syntax" <* pspc <*> pcurlies (psep (punc ";") psyntax)
  <|> DeclStack <$> pvariable <* punc "|-" <*> pcontextstack
  <|> ContractStack <$> pconditions <* pspc
                    <*> ((,,) <$> pvariable <* punc "|-" <*> pvariable <* punc "->" <*> pvariable)
                    <* pspc <*> pconditions
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <* pspc <*> pcurlies (psep (punc ",") pmachinestep)
  <|> DeclOp <$ plit "operator" <* pspc <*> pcurlies (psep (punc ";") (panoperator "~>"))
  <|> DefnOp <$> pdefnop
  <|> DeclJudgementForm <$> pjudgementform
  <|> DeclRule <$> prule

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

type Globals = (Decls, Operators)

globals :: Context -> Globals
globals = (,) <$> asks declarations <*> asks operators

setGlobals :: Globals -> Context -> Context
setGlobals (decls, ops) = setDecls decls . setOperators ops

sdeclOps :: [CAnOperator] -> Elab ([AAnOperator], Globals)
sdeclOps [] = ([],) <$> asks globals
sdeclOps ((AnOperator (WithRange r opname) (objName, objDesc) paramDescs retDesc) : ops) = do
  opname <- do
    ctxt <- ask
    when (Map.member opname (operators ctxt)) $
      throwError (AlreadyDeclaredOperator r opname)
    pure (Operator opname)
  syndecls <- gets (Map.keys . syntaxCats)
  (objName, objBinder) <- case objName of
     Nothing -> pure (Nothing, Unused)
     Just objName -> do
       objName <- isFresh objName
       pure (Just objName , Used objName)
  (descPat, objDesc, ds) <- spatSemantics (atom "Semantics" 0) objDesc
  ovs <- asks objVars
  local (declare objBinder (ActVar IsNotSubject (ovs :=> objDesc)) . setDecls ds) $ do
    (paramDescs, ds) <- sparamdescs paramDescs
    retDesc <- local (setDecls ds) $ ssemanticsdesc retDesc
    let op = AnOperator opname objDesc paramDescs retDesc
    (ops, decls) <- local (addOperator op) $ sdeclOps ops
    pure (op : ops, decls)

scommand :: CCommand -> Elab (ACommand, Globals)
scommand = \case
  DeclJudge em jd p -> during (DeclJElaboration jd) $ do
    jd <- isFresh jd
    p <- sprotocol p
    local (declare (Used jd) (AJudgement em p)) $
      (DeclJudge em jd p,) <$> asks globals
  DefnJudge (jd, (), ch) a -> during (DefnJElaboration jd) $ do
    let rp = getRange jd <> getRange ch
    ch <- Channel <$> isFresh ch
    jd <- isJudgement jd
    a <- withChannel rp Rootwards ch (judgementProtocol jd) $ local (setElabMode Definition) (sact a)
    (DefnJudge (judgementName jd, judgementProtocol jd, ch) a,) <$> asks globals
  ContractJudge pres stm posts -> do
    pres  <- traverse scondition pres
    stm   <- scondition stm
    posts <- traverse scondition posts
    -- TODO : additional checks
    (ContractJudge pres stm posts,) <$> asks globals
  DeclSyntax syns -> do
    oldsyndecls <- gets (Map.keys . syntaxCats)
    let newsyndecls = map (theValue . fst) syns
    let syndecls = newsyndecls ++ oldsyndecls
    syns <- for syns $ \ syn@(cat, _) ->
              during (DeclaringSyntaxCat (theValue cat)) $
                traverse (ssyntaxdesc syndecls) syn
    forM_ syns (uncurry declareSyntax)
    (DeclSyntax (map (first theValue) syns),) <$> asks globals
  DeclStack stk stkTy -> do
    stk <- isFresh stk
    stkTy <- scontextstack stkTy
    local (declare (Used stk) (AStack stkTy)) $ do
      (DeclStack (Stack stk) stkTy,) <$> asks globals
  ContractStack pres (stk, lhs, rhs) posts -> do
    pres  <- traverse scondition pres
    (stk,_) <- isContextStack stk
    posts <- traverse scondition posts
    -- TODO : additional checks for `lhs`, `rhs`
    (ContractStack pres (stk, lhs, rhs) posts,) <$> asks globals
  Go a -> during ExecElaboration $ (,) . Go <$> local (setElabMode Execution) (sact a) <*> asks globals
  Trace ts -> (Trace ts,) <$> asks globals
  DeclOp ops -> first DeclOp <$> sdeclOps ops
  DefnOp (p, opargs, rhs) -> do
    ((p, opargs), ret, decls, hints) <- do
      -- this is the op applied to the object, not the outer op being extended
      let op = fst (head opargs)
      (AnOperator op obj _ ret) <- soperator op
      (mr1, p, decls, hints) <- spat (Term unknown obj) p
      (opargs, decls, hints) <- local (setDecls decls . setHints hints) $
                                sopargs obj opargs
      pure ((p, opargs), ret, decls, hints)
    rhs <- local (setDecls decls . setHints hints) $ stm DontLog ret rhs
    -- this is the outer op being extended
    let op = fst (last opargs)
--    trace (unwords [getOperator op, "-[", '\'':show p, show opargs, "~>", show rhs]) (pure ())
    let cl = Clause (toClause p (B0 <>< opargs) rhs)
    (DefnOp (op, cl),) <$> asks globals
  DeclJudgementForm j -> do
    (j , gs) <- sjudgementform j
    pure (DeclJudgementForm j, gs)

checkCompatiblePlaces :: [PLACE Concrete] ->
                    [(Variable, ASemanticsDesc)] ->
                    [(Variable, ASemanticsDesc)] ->
                    Elab ()
checkCompatiblePlaces places inputs outputs = do
  -- Make sure subject protocol can be found unambiguously
  let names = map fst places
  let citizenNames = [x | (x, CitizenPlace) <- places]
  let inputNames = map fst inputs
  let outputNames = map fst outputs
  whenLeft (allUnique names) $ \ a -> throwError $ DuplicatedPlace (getRange a) a
  inputNamesSet <- case allUnique inputNames of
    Left a -> throwError $ DuplicatedInput (getRange a) a
    Right as -> pure as
  outputNamesSet <- case allUnique outputNames of
    Left a -> throwError $ DuplicatedOutput (getRange a) a
    Right as -> pure as
  whenCons (Set.toList (Set.intersection inputNamesSet outputNamesSet)) $ \ a _ ->
    throwError $ BothInputOutput (getRange a) a
  whenCons (mismatch citizenNames inputNames outputNames) $ \ (v, m) _ ->
    throwError (ProtocolCitizenSubjectMismatch (getRange v) v m)
  where
    mismatch :: [Variable]
             -> [Variable]
             -> [Variable]
             -> [(Variable, Mode ())]
    mismatch cs is os =
      catMaybes $ alignWith check (sort cs)
                $ sortBy (compare `on` fst)
                $ map (, Input) is ++ map (, Output) os

    check :: These Variable (Variable, Mode ()) -> Maybe (Variable, Mode ())
    check (These a b) = (a, Subject ()) <$ guard (a /= fst b)
    check t = Just (mergeThese const (first (, Subject ()) t))


{-
Do not use operators to compute citizens from subjects.
Rather, transmit glued subject-citizen pairs,
when matching a subject, glue metavars to pattern vars
then use s => c clauses ub rules to constrain the citizen
the parent sent with the subject syntax.
-}

sjudgementform :: JUDGEMENTFORM Concrete -> Elab (JUDGEMENTFORM Abstract, Globals)
sjudgementform JudgementForm{..} = during (JudgementFormElaboration jname) $ do
  inputs <- concat <$> traverse subjects jpreconds  -- TODO: should really be the closure of this info
  let (outputs, operators) = partitionEithers jpostconds
  outputs <- concat <$> traverse subjects outputs
  checkCompatiblePlaces jplaces inputs outputs
  (protocol, subjectKinds)  <- bimap Protocol fold . unzip
    <$> traverse (citizenJudgement inputs outputs) jplaces
  jname <- isFresh jname
  local (declare (Used jname) (AJudgement jextractmode protocol)) $ do
      (operators, gs) <- sdeclOps =<< traverse (kindify subjectKinds) operators
      pure ((jextractmode, jname, protocol), gs)


  where
    subjects :: JUDGEMENT Concrete -> Elab [(Variable, ASemanticsDesc)]
    subjects (Judgement r name fms) = do
      IsJudgement{..} <- isJudgement name
      xs <- case halfZip (getProtocol judgementProtocol) fms of
        Just xs -> pure xs
        Nothing -> throwError $ JudgementWrongArity r judgementName judgementProtocol fms
      let ys = [ (fm, sem) | ((Subject _, sem), fm) <- xs ]
      forM ys $ \case
        -- TODO: should use something like `isSendableSubject`
        (CFormula (These _ (Var r x)), sem) -> pure (x, sem)
        (x, _) -> throwError $ UnexpectedNonSubject r x

    citizenJudgement :: [(Variable, ASemanticsDesc)] -> [(Variable, ASemanticsDesc)]
                     -> CPlace -> Elab (PROTOCOLENTRY Abstract, Map Variable CSyntaxDesc)
    citizenJudgement inputs outputs (name, place) = case place of
      CitizenPlace ->
        case (lookup name inputs, lookup name outputs) of
          (Just isem, Nothing) -> pure ((Input, isem), Map.empty)
          (Nothing, Just osem) -> pure ((Output, osem), Map.empty)
          _  -> error "Impossible in citizenJudgement"

      SubjectPlace rsyn sem -> do
        syndecls <- gets (Map.keys . syntaxCats)
        syn <- ssyntaxdesc syndecls rsyn
        sem <- ssemanticsdesc sem
        pure ((Subject syn, sem), Map.singleton name rsyn)

    kindify :: Map Variable CSyntaxDesc -> CAnOperator -> Elab CAnOperator
    kindify m op
      | Var _ x <- objDesc op
      , Just syn <- Map.lookup x m = pure (op { objDesc = syn})
      | otherwise = throwError (MalformedPostOperator (getRange (objDesc op)) (theValue (opName op)) (Map.keys m))


-- | sopargs desc cops
-- | desc: description of the object the cops are applied to
sopargs :: SyntaxDesc -> [COpPattern] -> Elab ([AOpPattern], Decls, Hints)
sopargs desc [] = ([],,) <$> asks declarations <*> asks binderHints
sopargs desc ((rop, args):xs) = do
  (AnOperator op obj ps ret) <- soperator rop
  compatibleInfos (theRange rop) (Known desc) (Known obj)
  (args, decls, hints) <- splat (getRange rop <> foldMap getRange args) ps args
  (rest, decls, hints) <- local (setDecls decls . setHints hints) $ sopargs ret xs
  pure ((op, args):rest, decls, hints)
 where
  splat :: Range -> [SyntaxDesc] -> [CPattern] -> Elab ([APattern], Decls, Hints)
  splat r [] [] = ([],,) <$> asks declarations <*> asks binderHints
  splat r (d:ds) (p:ps) = do
    (_, p, decls, hints) <- spat (Term unknown d) p
    (ps, decls, hints) <- local (setDecls decls . setHints hints) $ splat r ds ps
    pure (p:ps, decls, hints)
  splat r ds ps = do
    r <- pure $ case (ds, ps) of
           ([], (_:_)) -> foldMap getRange ps
           _ -> r
    throwError (InvalidOperatorArity r (theValue rop) ds ps)

soperator :: COperator -> Elab AAnOperator
soperator (WithRange r tag) = do
  ops <- asks operators
  case Map.lookup tag ops of
    Nothing -> throwError (NotAValidOperator r tag)
    Just (obj, params, ret) -> pure (AnOperator (Operator tag) obj params ret)

scommands :: [CCommand] -> Elab [ACommand]
scommands [] = pure []
scommands (c:cs) = do
  (c, ds) <- scommand c
  cs <- local (setGlobals ds) $ scommands cs
  pure (c:cs)

elaborate :: [CCommand] -> Either (WithStackTrace Complaint) ([WithStackTrace Warning], [ACommand], SyntaxTable)
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
              rbranch = Process opts [] rroot env New a () rroot
          in run opts (p { stack = stack :< LeftBranch Hole rbranch, root = lroot}) cs
  Trace xs -> let trac = guard (not $ quiet opts) >> fromMaybe (xs ++ tracing p) (tracingOption opts)
                  newOpts = opts { tracingOption = Just trac }
              in run newOpts (p { options = newOpts }) cs
  DefnOp (op, cl) -> run opts (p { stack = stack :< Extended op cl }) cs
  _ -> run opts p cs
