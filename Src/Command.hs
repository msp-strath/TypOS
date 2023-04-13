{-# LANGUAGE UndecidableInstances, OverloadedStrings #-}

module Command where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Bifunctor (bimap, first)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Traversable (for)
import Data.Foldable (asum)

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
import Machine.Steps
import Machine.Trace (Shots)
import Options
import Parse
import Pretty
import Syntax
import Term.Base
import Unelaboration.Monad (Unelab(..), Naming, subunelab, withEnv)
import Unelaboration (initDAEnv, declareChannel)
import Location

import Data.Char (isSpace)
import Operator
import Thin
import Operator.Eval (HeadUpData' (..))
import Hide (Hide(..))
import Scope (Scope(..))

type family DEFNPROTOCOL (ph :: Phase) :: *
type instance DEFNPROTOCOL Concrete = ()
type instance DEFNPROTOCOL Abstract = AProtocol

data STATEMENT (ph :: Phase)
  = Statement (JUDGEMENTNAME ph) [Variable]

data OPENTRY (ph :: Phase)
  = DeclOp (ANOPERATOR ph)
  | DefnOp (DEFNOP ph)

deriving instance
  ( Show (OPERATOR ph)
  , Show (SEMANTICSDESC ph)
  , Show (ACTORVAR ph)
  , Show (PATTERN ph)
  , Show (SOT ph)
  , Show (DEFNOP ph)
  ) => Show (OPENTRY ph)

data COMMAND (ph :: Phase)
  = DeclJudge ExtractMode (JUDGEMENTNAME ph) (PROTOCOL ph)
  | DefnJudge (JUDGEMENTNAME ph, DEFNPROTOCOL ph, CHANNEL ph) (ACTOR ph)
  | ContractJudge [STATEMENT ph] (STATEMENT ph) [STATEMENT ph]
  | DeclSyntax [(SYNTAXCAT ph, SYNTAXDESC ph)]
  | DeclStack (STACK ph) (ContextStack (SYNTAXDESC ph) (SEMANTICSDESC ph))
  | ContractStack [STATEMENT ph] (STACK ph, Variable, Variable) [STATEMENT ph]
  | Go (ACTOR ph)
  | Trace [MachineStep]
  | OpBlock [OPENTRY ph]
  | Typecheck (TERM ph) (SEMANTICSDESC ph)

deriving instance
  ( Show (JUDGEMENTNAME ph)
  , Show (CHANNEL ph)
  , Show (BINDER ph)
  , Show (ACTORVAR ph)
  , Show (SCRUTINEEVAR ph)
  , Show (SCRUTINEETERM ph)
  , Show (SYNTAXDESC ph)
  , Show (SEMANTICSDESC ph)
  , Show (SOT ph)
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

instance (Show k, Show v, Unelab k, Unelab v, UnelabEnv k ~ UnelabEnv v, Pretty (Unelabed k), Pretty (Unelabed v)) =>
  Display (ContextStack k v) where
  type DisplayEnv (ContextStack k v) = UnelabEnv k
  display = viaPretty

instance Display AProtocol where
  type DisplayEnv AProtocol = Naming
  display = viaPretty

instance Pretty CStatement where
  pretty (Statement jd vars) = hsep $ pretty jd : (pretty <$> vars)

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
    Typecheck t ty -> keyword "typecheck" <+> pretty t <+> ":" <+> pretty ty

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
    DeclStack stk stkTy -> DeclStack <$> subunelab stk <*> unelab stkTy
    ContractStack pres (stk, lhs, rhs) posts -> ContractStack <$> traverse subunelab pres
                                                <*> fmap (, lhs, rhs) (subunelab stk)
                                                <*> traverse subunelab posts
    Go a -> Go <$> withEnv initDAEnv (unelab a)
    Trace ts -> pure $ Trace ts
    Typecheck t ty -> Typecheck <$> unelab t <*> unelab ty

instance Unelab AStatement where
  type UnelabEnv AStatement = ()
  type Unelabed AStatement = CStatement
  unelab (Statement jd vars) = (`Statement` vars) <$> unelab jd

instance Display ACommand where
  type DisplayEnv ACommand = Naming
  display = viaPretty

pmachinestep :: Parser MachineStep
pmachinestep = asum $ map (\ s -> s <$ plit (render $ pretty s)) [minBound..maxBound]

pjudgeat :: Parser (Variable, (), Variable)
pjudgeat = (,,) <$> pvariable <*> ppunc "@" <*> pvariable

psyntax :: Parser (WithRange SyntaxCat, Raw)
psyntax = (,) <$> pwithRange patom <* ppunc "=" <*> psyntaxdecl

pstatement :: Parser CStatement
pstatement = Statement <$> pvariable <*> many (id <$ pspc <*> pvariable)

pconditions :: Parser [CStatement]
pconditions = pcurlies (psep (ppunc ",") pstatement)

pcommand :: Parser CCommand
pcommand
    = DeclJudge <$> pextractmode <*> pvariable <* ppunc ":" <*> pprotocol
  <|> DefnJudge <$> pjudgeat <* ppunc "=" <*> pACT
  <|> ContractJudge <$> pconditions <* pspc <*> pstatement <* pspc <*> pconditions
  <|> DeclSyntax <$ plit "syntax" <*> pcurlies (psep (ppunc ";") psyntax)
  <|> DeclStack <$> pvariable <* ppunc "|-" <*> pcontextstack
  <|> ContractStack <$> pconditions <* pspc
                    <*> ((,,) <$> pvariable <* ppunc "|-" <*> pvariable <* ppunc "->" <*> pvariable)
                    <* pspc <*> pconditions
  <|> Go <$ plit "exec" <* pspc <*> pACT
  <|> Trace <$ plit "trace" <*> pcurlies (psep (ppunc ",") pmachinestep)
  <|> OpBlock <$ plit "operator"
              <*> pcurlies (psep (ppunc ";") (DeclOp <$> panoperator <|> DefnOp <$> pdefnop))
  <|> Typecheck <$ plit "typecheck" <* pspc <*> pTM <* ppunc ":" <*> pTM

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

sdeclOp :: CAnOperator -> Elab (AAnOperator, Globals)
-- (objName : objDescPat) -[ opname (p0 : paramDesc0) ... ] : retDesc
-- e.g.
-- 1. (p : ['Sig a \x.b]) -[ 'snd ]         : {x = p -[ 'fst ]} b
-- 2. (f : ['Pi a \x.b])  -[ 'app (t : a) ] : {x = t} b
-- 3. (n : 'Nat)
--      -[ 'rec ('Nat\m.          p  : 'Semantics)
--              (                 pZ : {m = 'Zero} p)
--              ('Nat\m. {m}p\ih. pS : {m = ['Succ m]} p)
--       ] : {m = n} p
sdeclOp (AnOperator (objBinder, objDescPat) (WithRange r opname) paramDescs retDesc) = do
  opname <- do
    ctxt <- ask
    when (Map.member opname (operators ctxt)) $
      throwComplaint r (AlreadyDeclaredOperator opname)
    pure (Operator opname)
  syndecls <- gets (Map.keys . syntaxCats)
  objBinder <- traverse isFresh objBinder
  let objName = ActorMeta ACitizen <$> objBinder
  ovs <- asks objVars
  sem <- satom "Semantics"
  (descPat, ds, objDesc) <- spatSemantics0 sem objDescPat
  op <- local (declare objBinder (ActVar IsNotSubject (ovs :=> objDesc)) . setDecls ds) $ do
    (paramDescs, ds) <- sparamdescs paramDescs
    retDesc <- local (setDecls ds) $ sty retDesc
    pure $ AnOperator (objName, descPat) opname paramDescs retDesc
  local (addOperator op) $ (op,) <$> asks globals

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
  Typecheck t ty -> do
    ty <- sty ty
    t <- stm DontLog ty t
    g <- asks globals
    pure (Typecheck t ty, g)

  -- Sig S \x.T - 'fst ~> S
  -- (p : Sig S \x.T) - 'snd ~> {x=[ p - 'fst ]}T
  OpBlock ops -> first OpBlock <$> sopBlock ops

sopBlock :: [OPENTRY Concrete] -> Elab ([OPENTRY Abstract], Globals)
sopBlock [] = ([],) <$> asks globals
sopBlock (DefnOp (rp, opelims@((rpty,_,_):_), rhs) : rest) = do
  -- p : pty0 -[ opelim0 ] : pty1 -[ opelim1 ] ... : ptyn -[ opelimn ] ~> rhs
  (p, opelimz, decls, lhsTy) <- sopelims0 (getRange rp <> getRange rpty) rp opelims
  rhs <- local (setDecls decls) $ stm DontLog lhsTy rhs
  -- this is the outer op being extended
  let op = case opelimz of (_ :< (_, op, _)) -> op
  let cl = toClause p opelimz rhs
  (bl , gl) <- sopBlock rest
  pure (DefnOp (op, cl) : bl, gl)
sopBlock (DeclOp op : rest) = do
  (op, gl) <- sdeclOp op
  (bl, gl) <- local (setGlobals gl) $ sopBlock rest
  pure (DeclOp op : bl, gl)

sopelims0 :: Range
          -> RawP
          -> [(RawP, OPERATOR Concrete, [RawP])]
          -> Elab (Pat, Bwd (Pat, OPERATOR Abstract, [Pat]), Decls, ASemanticsDesc)
sopelims0 r = sopelims r B0 . Left

sopelims :: Range
         -> Bwd (Pat, OPERATOR Abstract, [Pat])
         -> Either RawP (Pat, (ASemanticsDesc, ACTm))
         -> [(RawP, OPERATOR Concrete, [RawP])]
         -> Elab (Pat, Bwd (Pat, OPERATOR Abstract, [Pat]), Decls, ASemanticsDesc)
sopelims r opelimz (Right (p, (inty, t))) [] = (p,opelimz,,inty) <$> asks declarations
sopelims r opelimz acc ((rpty, op, args):opelims) = do
  -- We need to worry about freshening up names in operator
  -- declarations when checking definitions to avoid clashes
  (AnOperator (mb, opat) opName pdescs rdesc) <- freshenOp =<< soperator op
  sem <- satom "Semantics"
  (pty, decls, inty) <- spatSemantics0 sem rpty
  (decls, (p,(inty, t))) <- local (setDecls decls) $ case acc of
    Left rp -> do
      (p, decls, t) <- spatSemantics0 inty rp
      pure (decls, (p, (inty, t)))
    Right x -> do
      -- TODO: check that the type in x matches pty
      pure (decls, x)

  -- TODO: check that pty is compatible with opat
  dat <- matchObjType r (mb, opat) (t, inty)
  let r' = getRange op <> foldMap getRange args
  local (setDecls decls . setHeadUpData dat) $ do
    ((outty, decls), (pargs, args)) <- spats r' (getOperator opName) pdescs args rdesc
    local (setDecls decls) $ do
        let acc = Right (p, (outty, rad t inty -% (getOperator opName, args)))
        sopelims (r <> r') (opelimz :< (pty, opName, pargs)) acc opelims

  where


    -- cf. sparam
    sparamSemantics :: Binder ActorMeta
                    -> Bwd String
                    -> Telescopic ASemanticsDesc
                    -> RawP
                    -> Elab ((Pat, ACTm), Decls, HeadUpData' ActorMeta)
    sparamSemantics binder namez (Stop pdesc) rp = do
      (p, decls, t) <- spatSemantics0 pdesc rp
      dat <- do
        dat <- asks headUpData
        pure $ case binder of
          Unused _ -> dat
          Used v  ->
           let env = huEnv dat
               env' = newActorVar v (namez <>> [], t) env
           in dat {huEnv = env'}
      pure ((p, t), decls, dat)
    sparamSemantics binder namez
      (Tele desc (Scope (Hide name) tele))
      (LamP r (Scope (Hide x) rp)) =
      elabUnder (x, desc) $ sparamSemantics binder (namez :< name) tele rp

    -- cf. itms
    spats :: Range
          -> String
          -> [(Binder ActorMeta, ASOT)]
          -> [CPattern]
          -> ASemanticsDesc
          -> Elab ((ASemanticsDesc, Decls), ([APattern], [ACTm]))
    spats r op [] [] rdesc = (,([], [])) <$> ((,) <$> instantiateDesc r rdesc <*> asks declarations)
    spats r op ((binder, sot) : bs) (rp:rps) rdesc = do
      (ovs :=> desc) <- instantiateSOT (getRange rp) sot
      ((p, t), decls, dat) <- sparamSemantics binder B0 (discharge ovs desc) rp
      local (setDecls decls . setHeadUpData dat) $
        fmap (bimap (p:) (t:)) <$> spats r op bs rps rdesc
    spats r op bs rps rdesc = throwComplaint r $ ArityMismatchInOperator op ((length bs) - (length rps))

{-
-- | sopargs desc cops
-- | desc: description of the object the cops are applied to
sopargs :: SyntaxDesc -> [COpPattern] -> Elab ([AOpPattern], Decls, Hints)
sopargs desc [] = ([],,) <$> asks declarations <*> asks binderHints
sopargs desc ((rop, args):xs) = do
  (AnOperator obj op ps ret) <- soperator rop
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
    throwComplaint r (InvalidOperatorArity (theValue rop) ds ps)
-}

freshenOp :: AAnOperator -> Elab AAnOperator
freshenOp (AnOperator (mp, p) opName pdesc rdesc) = do
  n <- gets clock
  modify (\ st -> st { clock = 1+n })
  let tick = ((show n ++) <$>)
  let tickCdB = ((tick <$>) $^)
  let tick' (ObjVars ovs :=> t) =
        ObjVars (fmap (tickCdB <$>) ovs) :=> tickCdB t
  pure $ AnOperator
    { objDesc = (tick <$> mp, tick <$> p)
    , opName
    , paramsDesc = map (bimap (tick <$>) tick') pdesc
    , retDesc = tickCdB rdesc
    }

soperator :: COperator -> Elab AAnOperator
soperator (WithRange r tag) = do
  ops <- asks operators
  case Map.lookup tag ops of
    Nothing -> throwComplaint r (NotAValidOperator tag)
    Just anop -> pure anop

scommands :: [CCommand] -> Elab [ACommand]
scommands [] = pure []
scommands (c:cs) = do
  (c, ds) <- scommand c
  cs <- local (setGlobals ds) $ scommands cs
  pure (c:cs)

elaborate :: Options -> [CCommand]
          -> Either (WithStackTrace (WithRange Complaint))
                    ([WithStackTrace (WithRange Warning)], [ACommand], SyntaxTable)
elaborate opts ccs = evalElab opts $ do
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
  OpBlock ops ->
    let clauses = flip concatMap ops $ \case
          DefnOp (op, cl) -> [Extended op cl]
          DeclOp{} -> [] in
    let stack' = stack <>< clauses in
    run opts (p { stack = stack' }) cs
  _ -> run opts p cs
