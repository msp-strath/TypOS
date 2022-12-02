module Elaboration where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Function
import Data.List (isPrefixOf)
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Bitraversable

import Actor
import Bwd
import Concrete.Base
import Format
import Hide
import Scope
import Syntax
import Thin
import Utils
import Info

import Elaboration.Monad
import Term.Base
import qualified Term.Base as Term
import Term.Substitution
import Pattern as P
import Location
import Data.List.NonEmpty (fromList)
import Pattern.Coverage (Covering'(..), combine, shrinkBy, missing)
import Control.Applicative ((<|>))
import Operator
import qualified Semantics

isSubject :: EScrutinee -> IsSubject' ()
isSubject SubjectVar{} = IsSubject ()
isSubject _ = IsNotSubject

-- must be used in definition mode only
checkSendableSubject :: Raw -> Elab (Maybe ActorVar)
checkSendableSubject tm = do
  localVars <- asks (getObjVars . objVars)
  go (fmap objVarName localVars) tm
  where
  go :: Bwd String -> Raw -> Elab (Maybe ActorVar)
  go localVars x = case x of
    Var r v -> resolve v >>= \case
      Just (Left (ActVar (IsSubject {}) _)) -> pure . Just $ getVariable v
      _ -> Nothing <$ raiseWarning (SentSubjectNotASubjectVar (getRange tm) tm)
    Sbst r sg x -> do
      case isInvertible localVars sg of
        Nothing -> Nothing <$ raiseWarning (SentSubjectNotASubjectVar (getRange tm) tm)
        Just localVars -> go localVars x
    _ -> Nothing <$ raiseWarning (SentSubjectNotASubjectVar (getRange tm) tm)
  isInvertible :: Bwd String -> Bwd SbstC -> Maybe (Bwd String)
  isInvertible lvz B0 = pure lvz
  isInvertible (lvz :< w) (sz :< Keep _ v) | getVariable v == w
    = (:< w) <$> isInvertible lvz sz
  isInvertible (lvz :< w) (sz :< Drop _ v) | getVariable v == w
    = isInvertible lvz sz
  isInvertible lvz (sz :< Assign _ v (Var _ w)) | Just (lz, x, ls) <- focus (getVariable w) lvz
    = (:< getVariable v) <$> isInvertible (lz <>< ls) sz
  isInvertible _ _ = Nothing

escrutinee :: EScrutinee -> SyntaxDesc
escrutinee = \case
  Pair _ p q -> Syntax.contract (VCons (escrutinee p) (escrutinee q))
  SubjectVar _ desc -> desc
  Lookup _ desc _ -> desc
  Compare _ _ _ -> Syntax.contract (VEnumOrTag ["LT", "EQ", "GT"] [])
  Term _ desc -> desc

dual :: PROTOCOL ph -> PROTOCOL ph
dual (Protocol ps) = Protocol $ flip map ps $ \case
  (Input, c) -> (Output, c)
  (Subject x, c) -> (Subject x, c)
  (Output, c) -> (Input, c)

data Comm = SEND | RECV
  deriving (Eq, Show)

whatComm :: Mode a -> Direction -> Comm
whatComm m d = case m of
  Input -> RECV
  Subject _ -> case d of
    Rootwards -> RECV
    Leafwards -> SEND
  Output -> SEND

isFresh :: Variable -> Elab String
isFresh x = do
  res <- resolve x
  whenJust res $ \ _ -> throwError (VariableShadowing (getRange x) x)
  pure (getVariable x)

spassport :: Usage -> IsSubject -> Passport
spassport u IsSubject{} | isBeingScrutinised u = ASubject
spassport _ _ = ACitizen

svar :: Usage -> Variable -> Elab (IsSubject, Info ASemanticsDesc, ACTm)
svar usage x = do
  ovs <- asks objVars
  res <- resolve x
  case res of
    Just (Left k) -> case k of
      ActVar isSub (sc :=> desc) -> case sc `thinsTo` ovs of
        Just th -> do
          logUsage (getVariable x) usage
          pure (isSub, desc, ActorMeta (spassport usage isSub) (getVariable x) $: sbstW (sbst0 0) th)
        Nothing -> throwError (MetaScopeTooBig (getRange x) x sc ovs)
      _ -> throwError (NotAValidTermVariable (getRange x) x k)
    Just (Right (desc, i)) -> pure (IsNotSubject, desc, var i (scopeSize ovs))
    Nothing -> throwError (OutOfScope (getRange x) x)

spop :: Range -> Elab (ObjVars, (Variable, Info ASemanticsDesc))
spop r = do
  ovs <- asks objVars
  case getObjVars ovs of
    B0 -> throwError (EmptyContext r)
    (xz :< ObjVar x cat) -> pure (ObjVars xz, (Variable r x, cat))

ssyntaxdesc :: [SyntaxCat] -> Raw -> Elab SyntaxDesc
ssyntaxdesc syndecls syn = do
  let desc = catToDesc "Syntax"
  syn <- withSyntax (syntaxDesc syndecls) $ stm DontLog desc syn
  case isMetaFree syn of
    Nothing -> error "Impossible in ssyntaxdesc" -- this should be impossible, since parsed in empty context
    Just syn0 -> pure syn0

ssemanticsdesc :: CSemanticsDesc -> Elab ASemanticsDesc
ssemanticsdesc sem = do
  syndecls <- gets (Map.keys . syntaxCats)
  ssyntaxdesc ("Semantics":syndecls) sem
  -- TODO: use stm to actually be able to use operators & actor vars
  -- DontLog (catToDesc "Semantics")

ssbst :: Usage -> Bwd SbstC -> Elab (ACTSbst, ObjVars)
ssbst usage B0 = do
    ovs <- asks objVars
    pure (sbstI (scopeSize ovs), ovs)
ssbst usage (sg :< sgc) = case sgc of
    Keep r v -> do
      (xz, (w, cat)) <- spop r
      when (v /= w) $ throwError (NotTopVariable r v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst usage sg)
      pure (sbstW sg (ones 1), ovs <: ObjVar (getVariable w) cat)
    Drop r v -> do
      (xz, (w, cat)) <- spop r
      when (v /= w) $ throwError (NotTopVariable r v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst usage sg)
      pure (weak sg, ovs)
    Assign r v t -> do
      info <- getHint (getVariable v)
      desc <- fromInfo r info
      t <- stm usage desc t
      (sg, ovs) <- ssbst usage sg
      v <- local (setObjVars ovs) $ isFresh v
      pure (sbstT sg ((Hide v :=) $^ t), ovs <: ObjVar v info)

sth :: (Bwd Variable, ThDirective) -> Elab Th
sth (xz, b) = do
  ovs <- asks objVars
  let th = which (`elem` (getVariable <$> xz)) (objVarName <$> getObjVars ovs)
  pure $ case b of
    ThKeep -> th
    ThDrop -> comp th

stms :: Usage -> [SyntaxDesc] -> Raw -> Elab ACTm
stms usage [] (At r "") = atom "" <$> asks (length . objVars)
stms usage [] (At r a) = throwError (ExpectedNilGot r a)
stms usage [] t = throwError (ExpectedANilGot (getRange t) t)
stms usage (d:ds) (Cons r p q) = (%) <$> stm usage d p <*> stms usage ds q
stms usage _ t = throwError (ExpectedAConsGot (getRange t) t)

sscrutinee :: CScrutinee -> Elab (EScrutinee, AScrutinee)
sscrutinee (SubjectVar r v) = do
  (isSub, info, actm) <- svar (Scrutinised r) v
  desc <- fromInfo r info
  case (isSub, actm) of
    (IsSubject{}, CdB (m :$ sg) _) -> pure (SubjectVar r desc, SubjectVar r actm)
    _ -> throwError (NotAValidSubjectVar r v)
sscrutinee (Pair r sc1 sc2) = do
  (esc1, asc1) <- sscrutinee sc1
  (esc2, asc2) <- sscrutinee sc2
  pure (Pair r esc1 esc2, Pair r asc1 asc2)
sscrutinee (Lookup r stk v) = do
  (stk, stkTy) <- isContextStack stk
  t <- during (LookupVarElaboration v) $ do
    (isSub, info, t) <- svar (LookedUp r) v
    void $ compatibleInfos r (Known (keyDesc stkTy)) info
    pure t
  let desc = Syntax.contract (VEnumOrTag ["Nothing"] [("Just", [valueDesc stkTy])])
  pure (Lookup r desc (getVariable v), Lookup r stk t)
sscrutinee (Compare r s t) = do
  infoS <- guessDesc False s
  infoT <- guessDesc False t
  desc <- during (CompareSyntaxCatGuess s t) $
      fromInfo r =<< compatibleInfos r infoS infoT
  s <- during (CompareTermElaboration s) $ stm (Compared (getRange s)) desc s
  t <- during (CompareTermElaboration t) $ stm (Compared (getRange t)) desc t
  pure (Compare r () (), Compare r s t)
sscrutinee (Term r t) = during (ScrutineeTermElaboration t) $ do
  desc <- fromInfo r =<< guessDesc False t
  t <- stm (MatchedOn r) desc t
  pure (Term r desc, Term r t)


stm :: Usage -> ASemanticsDesc -> Raw -> Elab ACTm
stm usage desc (Var r v) = during (TermVariableElaboration v) $ do
  table <- gets syntaxCats
  (_, desc', t) <- svar usage v
  compatibleInfos (getRange v) (Known desc) desc'
  pure t
stm usage desc (Sbst r sg t) = do
    (sg, ovs) <- during (SubstitutionElaboration sg) $ ssbst usage sg
    t <- local (setObjVars ovs) (stm usage desc t)
    pure (t //^ sg)
stm usage desc rt = do
  table <- gets syntaxCats
  case Syntax.expand table desc of
    Nothing -> throwError (InvalidSyntaxDesc (getRange rt) desc)
    Just vdesc -> case rt of
      At r a -> do
        case vdesc of
          VAtom -> pure ()
          VAtomBar as -> when (a `elem` as) $ throwError (GotBarredAtom r a as)
          VNil -> unless (a == "") $ throwError (ExpectedNilGot r a)
          VNilOrCons{} -> unless (a == "") $ throwError (ExpectedNilGot r a)
          VEnumOrTag es _ -> unless (a `elem` es) $ throwError (ExpectedEnumGot r es a)
          VWildcard -> pure ()
          _ -> throwError (SyntaxError r desc rt)
        atom a <$> asks (length . objVars)
      Cons r p q -> case vdesc of
        VNilOrCons d1 d2 -> (%) <$> stm usage d1 p <*> stm usage d2 q
        VCons d1 d2 -> (%) <$> stm usage d1 p <*> stm usage d2 q
        VWildcard -> (%) <$> stm usage desc p <*> stm usage desc q
        VEnumOrTag _ ds -> case p of
          At r a -> case lookup a ds of
            Nothing -> throwError (ExpectedTagGot r (fst <$> ds) a)
            Just descs -> (%) <$> stm usage (atom "Atom" 0) p <*> stms usage descs q
          _ -> throwError (SyntaxError r desc rt)
        _ -> throwError (SyntaxError r desc rt)
      Lam r (Scope (Hide x) sc) -> do
        (s, desc) <- case vdesc of
          VWildcard -> pure (Unknown, desc)
          VBind cat desc -> pure (Known (catToDesc cat), desc)
          _ -> throwError (SyntaxError r desc rt)
        case x of
          Used x -> do
            x <- isFresh x
            sc <- local (declareObjVar (x, s)) $ stm usage desc sc
            pure (x \\ sc)
          Unused -> do
            sc <- stm usage desc sc
            pure ((Hide "_" := False :.) $^ sc)
      Op r rs ro -> case ro of
        -- TODO: usage checking
        At ra a -> do
          (sdesc, psdesc, rdesc) <- isOperator ra a
          unless (null psdesc) $ throwError (ExpectedAnEmptyListGot r a psdesc)
          o <- stm usage (Syntax.contract VAtom) ro
          s <- stm usage sdesc rs
          compatibleInfos r (Known rdesc) (Known desc)
          pure (Term.contract (s :-: o))
        Cons rp (At ra a) ps -> do
          (sdesc, psdesc, rdesc) <- isOperator ra a
          o <- stms usage (Syntax.contract VAtom : psdesc) ro
          s <- stm usage sdesc rs
          compatibleInfos r (Known rdesc) (Known desc)
          pure (Term.contract (s :-: o))
        _ -> throwError (ExpectedAnOperator (getRange ro) ro)


spats :: IsSubject -> [SyntaxDesc] -> RawP -> Elab (Maybe Range, Pat, Decls, Hints)
spats _ [] (AtP r "") = (Nothing, AP "",,) <$> asks declarations <*> asks binderHints
spats _ [] (AtP r a) = throwError (ExpectedNilGot r a)
spats _ [] t = throwError (ExpectedANilPGot (getRange t) t)
spats isSub (d:ds) (ConsP r p q) = do
  (mr1, p, decls, hints) <- spatBase isSub d p
  (mr2, q, decls, hints) <- local (setDecls decls . setHints hints) $ spats isSub ds q
  pure (mr1 <|> mr2, PP p q, decls, hints)
spats _ _ t = throwError (ExpectedAConsPGot (getRange t) t)

-- Returns:
-- 0. Whether a subject pattern was thrown away
-- 1. Elaborated pattern
-- 2. Bound variables (together with their syntactic categories)
-- 3. Binder hints introduced by \x. patterns
spat :: EScrutinee -> RawP -> Elab (Maybe Range, Pat, Decls, Hints)
spat esc rp@(AsP r v p) = do
  unless (isSubjectFree esc) $
    throwError (AsPatternCannotHaveSubjects r rp)
  let desc = escrutinee esc
  v <- isFresh v
  ds <- asks declarations
  ovs <- asks objVars
  (mr, p, ds, hs) <- local (setDecls (ds :< (v, ActVar IsNotSubject (Known desc) ovs))) $ spat esc p
  pure (mr, AT (ActorMeta ACitizen v) p, ds, hs)
spat esc p@VarP{} = spatBase (Pattern <$ isSubject esc) (escrutinee esc) p
spat esc (ThP r th p) = do
  th <- sth th
  (mr, p, ds, hs) <- local (th ^?) $ spat esc p
  pure (mr, p *^ th, ds, hs)
spat esc p@(UnderscoreP r) = do
  (_, p, ds, hs) <- spatBase (Pattern <$ isSubject esc) (escrutinee esc) p
  let mr = r <$ guard (not (isSubjectFree esc))
  pure (mr, p, ds, hs)
spat esc@(Pair r esc1 esc2) rp = case rp of
  ConsP r p q -> do
    (mr1, p, ds, hs) <- spat esc1 p
    (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spat esc2 q)
    pure (mr1 <|> mr2, PP p q, ds, hs)
  _ -> throwError (SyntaxPError (getRange rp) (escrutinee esc) rp)
spat (SubjectVar r desc) rp = spatBase (IsSubject Pattern) desc rp
spat esc@(Lookup _ _ av) rp@(ConsP r (AtP _ "Just") (ConsP _ _ (AtP _ ""))) = do
  logUsage av (SuccessfullyLookedUp r)
  spatBase IsNotSubject (escrutinee esc) rp
spat esc@(Lookup _ _ av) rp = spatBase IsNotSubject (escrutinee esc) rp
spat esc@(Compare{}) rp = spatBase IsNotSubject (escrutinee esc) rp
spat esc@(Term{}) rp = spatBase IsNotSubject (escrutinee esc) rp

spatBase :: IsSubject -> ASemanticsDesc -> RawP -> Elab (Maybe Range, Pat, Decls, Hints)
spatBase isSub desc rp@(AsP r v p) = do
  unless (isSub == IsNotSubject) $
    throwError (AsPatternCannotHaveSubjects r rp)
  v <- isFresh v
  ds <- asks declarations
  ovs <- asks objVars
  (mr, p, ds, hs) <- local (setDecls (ds :< (v, ActVar isSub (ovs :=> desc)))) $ spatBase isSub desc p
  pure (mr, AT (ActorMeta ACitizen v) p, ds, hs)
spatBase isSub desc (ThP r th p) = do
  th <- sth th
  (mr, p, ds, hs) <- local (th ^?) $ spatBase isSub desc p
  pure (mr, p *^ th, ds, hs)
spatBase isSub desc (VarP r v) = during (PatternVariableElaboration v) $ do
  table <- gets syntaxCats
  ds <- asks declarations
  hs <- asks binderHints
  res <- resolve v
  case res of
    Just (Left k)  -> throwError (NotAValidPatternVariable r v k)
    Just (Right (desc', i)) -> do
      compatibleInfos (getRange v) (Known desc) desc'
      pure (Nothing, VP i, ds, hs)
    Nothing -> do
      ovs <- asks objVars
      v <- pure (getVariable v)
      let pat = MP (ActorMeta (spassport (Scrutinised unknown) isSub) v) (ones $ scopeSize ovs)
      pure (Nothing, pat, ds :< (v, ActVar isSub (ovs :=> desc)), hs)
spatBase isSub desc (UnderscoreP r) = do
  let mr = case isSub of
             IsSubject{} -> Just r
             IsNotSubject -> Nothing
  (mr,HP,,) <$> asks declarations <*> asks binderHints
spatBase isSub desc rp = do
  table <- gets syntaxCats
  case Syntax.expand table desc of
    Nothing -> throwError (InvalidSyntaxDesc (getRange rp) desc)
    Just vdesc -> case rp of
      AtP r a -> do
        case vdesc of
          VAtom -> pure ()
          VAtomBar as -> when (a `elem` as) $ throwError (GotBarredAtom r a as)
          VNil -> unless (a == "") $ throwError (ExpectedNilGot r a)
          VNilOrCons{} -> unless (a == "") $ throwError (ExpectedNilGot r a)
          VEnumOrTag es _ -> unless (a `elem` es) $ throwError (ExpectedEnumGot r es a)
          VWildcard -> pure ()
          _ -> throwError (SyntaxPError r desc rp)
        (Nothing, AP a,,) <$> asks declarations <*> asks binderHints

      ConsP r p q -> case vdesc of
        VNilOrCons d1 d2 -> do
          (mr1, p, ds, hs) <- spatBase isSub d1 p
          (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spatBase isSub d2 q)
          pure (mr1 <|> mr2, PP p q, ds, hs)
        VCons d1 d2 -> do
          (mr1, p, ds, hs) <- spatBase isSub d1 p
          (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spatBase isSub d2 q)
          pure (mr1 <|> mr2, PP p q, ds, hs)
        VWildcard -> do
          (mr1, p, ds, hs) <- spatBase isSub desc p
          (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spatBase isSub desc q)
          pure (mr1 <|> mr2, PP p q, ds, hs)
        VEnumOrTag _ ds -> case p of
          AtP r a -> case lookup a ds of
            Nothing -> throwError (ExpectedTagGot r (fst <$> ds) a)
            Just descs ->  do
              (mr1, p, ds, hs) <- spatBase isSub (atom "Atom" 0) p
              (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spats isSub descs q)
              pure (mr1 <|> mr2, PP p q, ds, hs)
          _ -> throwError (SyntaxPError r desc rp)
        _ -> throwError (SyntaxPError r desc rp)

      LamP r (Scope v@(Hide x) p) -> do
        (s, desc) <- case vdesc of
          VWildcard -> pure (Unknown, desc)
          VBind cat desc -> pure (Known (catToDesc cat), desc)
          _ -> throwError (SyntaxPError r desc rp)

        case x of
          Unused -> do
            (mr, p, ds, hs) <- spatBase isSub desc p
            pure (mr, BP (Hide "_") p, ds, hs)
          Used x -> do
            x <- isFresh x
            (mr, p, ds, hs) <- local (declareObjVar (x, s) . addHint x s) $ spatBase isSub desc p
            pure (mr, BP (Hide x) p, ds, hs)

isChannel :: Variable -> Elab Channel
isChannel ch = resolve ch >>= \case
  Just (Left (AChannel sc)) -> pure (Channel $ getVariable ch)
  Just mk -> throwError (NotAValidChannel (getRange ch) ch $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope (getRange ch) ch)

isOperator :: Range -> String -> Elab (SyntaxDesc, [SyntaxDesc], ASemanticsDesc)
isOperator r nm = do
  ops <- asks operators
  case Map.lookup nm ops of
    Just res -> pure res
    Nothing -> throwError (NotAValidOperator r nm)

data IsJudgement = IsJudgement
  { judgementExtract :: ExtractMode
  , judgementName :: JudgementName
  , judgementProtocol :: AProtocol
  }

isJudgement :: Variable -> Elab IsJudgement
isJudgement jd = resolve jd >>= \case
  Just (Left (AJudgement em p)) -> pure (IsJudgement em (getVariable jd) p)
  Just mk -> throwError (NotAValidJudgement (getRange jd) jd $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope (getRange jd) jd)

isContextStack :: Variable -> Elab (Stack, AContextStack)
isContextStack stk = resolve stk >>= \case
  Just (Left (AStack stkTy)) -> pure (Stack (getVariable stk), stkTy)
  Just mk -> throwError (NotAValidStack (getRange stk) stk $ either Just (const Nothing) mk)
  Nothing -> throwError (OutOfScope (getRange stk) stk)


channelScope :: Channel -> Elab ObjVars
channelScope (Channel ch) = do
  ds <- asks declarations
  case fromJust (focusBy (\ (y, k) -> k <$ guard (ch == y)) ds) of
    (_, AChannel sc, _) -> pure sc

steppingChannel :: Range -> Channel
                -> (Direction -> [AProtocolEntry] -> Elab (a, [AProtocolEntry]))
                -> Elab a
steppingChannel r ch step = do
  nm <- getName
  (dir, pnm, p) <- gets (fromJust . channelLookup ch)
  unless (pnm `isPrefixOf` nm) $ throwError (NonLinearChannelUse r ch)
  (cat, p) <- step dir p
  modify (channelInsert ch (dir, nm, p))
  pure cat

open :: Direction -> Channel -> AProtocol -> Elab ()
open dir ch (Protocol p) = do
  nm <- getName
  modify (channelInsert ch (dir, nm, p))

close :: Bool -> Range -> Channel -> Elab ()
close b r ch = do
  -- make sure the protocol was run all the way
  gets (channelLookup ch) >>= \case
    Just (_, _, ps) -> case ps of
      [] -> pure ()
      _ -> when b $
            -- if we cannot win, we don't care
            throwError (UnfinishedProtocol r ch (Protocol ps))
  modify (channelDelete ch)

withChannel :: Range -> Direction -> Channel -> AProtocol -> Elab a -> Elab a
withChannel r dir ch@(Channel rch) p ma = do
  open dir ch p
  -- run the actor in the extended context
  ovs <- asks objVars
  (a, All b) <- local (declare (Used rch) (AChannel ovs)) $ listen ma
  close b r ch
  pure a

guessDesc :: Bool -> -- is this in tail position?
             Raw -> Elab (Info ASemanticsDesc)
guessDesc b (Var _ v) = resolve v >>= \case
  Just (Right (info, i)) -> pure info
  Just (Left (ActVar isSub (ObjVars B0 :=> desc))) -> pure $ Known desc
  _ -> pure Unknown
guessDesc b (Cons _ p q) = do
  dp <- guessDesc False p
  dq <- guessDesc True q
  case (dp, dq) of
    (Known d1, Known d2) -> pure (Known $ Semantics.contract (VCons d1 d2))
    _ -> pure Unknown
-- might need better guess for the scope than 0
guessDesc True (At _ "") = pure (Known $ Semantics.contract (VNil 0))
guessDesc _ _ = pure Unknown

compatibleChannels :: Range -> (Direction, [AProtocolEntry]) -> Ordering -> (Direction, [AProtocolEntry]) -> Elab Int
compatibleChannels r (dp, []) dir (dq, []) = pure 0
compatibleChannels r (dp, p@(m, s) : ps) dir (dq, q@(n, t) : qs) = do
  unless (s == t) $ throwError (IncompatibleSyntaxDescs r s t)
  let (cp , cq) = (whatComm m dp, whatComm n dq)
  when (cp == cq) $ throwError (IncompatibleModes r p q)
  case (cp, dir) of
    (RECV, LT) -> throwError (WrongDirection r p dir q)
    (SEND, GT) -> throwError (WrongDirection r p dir q)
    _ -> pure ()
  (+1) <$> compatibleChannels r (dp, ps) dir (dq , qs)
compatibleChannels r (_,ps) _ (_,qs) = throwError (ProtocolsNotDual r (Protocol ps) (Protocol qs))

sirrefutable :: String -> IsSubject -> RawP -> Elab (Binder String, Maybe (CScrutinee, RawP))
sirrefutable nm isSub = \case
  VarP _ v -> (, Nothing) . Used <$> isFresh v
  UnderscoreP _ -> pure (Unused, Nothing)
  p -> do ctxt <- ask
          -- this should be a unique name & is not user-writable
          let r = getRange p
          let av = "&" ++ nm ++ show (length (objVars ctxt) + length (declarations ctxt))
          let var = Variable r av
          let sc = case isSub of
                     IsSubject{} -> SubjectVar r var
                     IsNotSubject -> Term r (Var r var)
          pure (Used av, Just (sc, p))

checkScrutinised :: Binder String -> Elab Bool
checkScrutinised Unused = pure False
checkScrutinised (Used nm) = do
  avs <- gets actvarStates
  b <- case Map.lookup nm avs of
    Just logs | wasScrutinised logs -> pure True
    _ -> pure False
  modify (\ st -> st { actvarStates = Map.delete nm (actvarStates st) })
  pure b

sact :: CActor -> Elab AActor
sact = \case
  Win r -> pure (Win r)
  Constrain r s t -> do
    infoS <- guessDesc False s
    infoT <- guessDesc False t
    desc <- during (ConstrainSyntaxCatGuess s t) $
      fromInfo r =<< compatibleInfos r infoS infoT
    s <- during (ConstrainTermElaboration s) $ stm (Constrained (getRange s)) desc s
    t <- during (ConstrainTermElaboration t) $ stm (Constrained (getRange t)) desc t
    pure $ Constrain r s t

  Branch r a b -> do
    a <- local (turn West) $ sact a
    b <- local (turn East) $ sact b
    pure (Branch r a b)

  Spawn r em jd ch a -> do
    let rp = getRange jd <> getRange ch
    -- check the channel name is fresh & initialise it
    ch <- Channel <$> isFresh ch
    jd <- isJudgement jd

    a <- withChannel rp Leafwards ch (dual $ judgementProtocol jd) $ sact a

    em <- pure $ case em of
      AlwaysExtract -> judgementExtract jd
      _ -> em

    pure $ Spawn r em (judgementName jd) ch a

  Send r ch () tm a -> do
    ch <- isChannel ch
    -- Check the channel is in sending mode, & step it
    (m, desc) <- steppingChannel r ch $ \ dir -> \case
      (m, desc) : p | whatComm m dir == SEND -> pure ((m, desc), p)
      _ -> throwError (InvalidSend r ch tm)

    (usage, gd) <- do
      case m of
        Output -> pure (SentInOutput r, Nothing)
        Subject _ -> ((SentAsSubject r ,) <$>) $ asks elabMode >>= \case
          Execution  -> pure Nothing
          Definition -> checkSendableSubject tm

    -- Send
    tm <- during (SendTermElaboration ch tm) $ do
      sc <- channelScope ch
      ovs <- asks objVars
      -- NB: the lintersection takes the (Info ASemanticsDesc) into account
      -- Should it?
      let (thx, xyz, thy) = lintersection sc ovs
      (*^ thx) <$> local (setObjVars xyz) (stm usage desc tm)

    a <- sact a
    pure $ Send r ch gd tm a

  Recv r ch (p, a) -> do
    ch <- isChannel ch

    -- Check the channel is in receiving mode & step it
    (m, cat) <- steppingChannel r ch $ \ dir -> \case
      (m, cat) : p | whatComm m dir == RECV -> pure ((m, cat), p)
      _ -> throwError (InvalidRecv r ch p)

    let isSub = case m of
           Subject _ -> IsSubject Parent
           _ -> IsNotSubject

    -- elaborate the (potentially pattern-matching) receive
    (av, pat) <- during (RecvMetaElaboration ch) $ sirrefutable "recv" isSub p

    -- Further actor
    sc <- channelScope ch
    (a, All canwin) <- local (declare av (ActVar isSub (Known cat) sc))
           $ listen
           $ sact
           $ case pat of
               Nothing -> a
               Just (sc, p) -> Match r sc [(p, a)]

    -- Check we properly scrutinised a subject input
    unlessM (checkScrutinised av) $
      when (isSubjectMode m) $ do
        when canwin $ raiseWarning (RecvSubjectNotScrutinised r ch av)

    pure $ Recv r ch (ActorMeta (spassport (Scrutinised unknown) isSub) <$> av, a)

  Connect r (CConnect ch1 ch2) -> during (ConnectElaboration ch1 ch2) $ do
    ch1 <- isChannel ch1
    ch2 <- isChannel ch2
    p <- steppingChannel r ch1 $ \ dir p -> pure ((dir,p), [])
    q <- steppingChannel r ch2 $ \ dir p -> pure ((dir,p), [])
    sc1 <- channelScope ch1
    sc2 <- channelScope ch2
    (dir, th) <- case (findSub sc1 sc2, findSub sc2 sc1) of
      (Just thl, Just thr) -> pure (EQ, thl)
      (Just thl, _) -> pure (LT, thl)
      (_, Just thr) -> pure (GT, thr)
      _ -> throwError (IncompatibleChannelScopes r sc1 sc2)
    steps <- compatibleChannels r p dir q
    pure (aconnect r ch1 th ch2 steps)

  FreshMeta r desc (av, a) -> do
    (desc, av, ovs) <- during FreshMetaElaboration $ do
      syndecls <- gets (Map.keys . syntaxCats)
      desc <- ssyntaxdesc syndecls desc
      av <- isFresh av
      ovs <- asks objVars
      pure (desc, av, ovs)
    a <- local (declare (Used av) (ActVar IsNotSubject (Known desc) ovs)) $ sact a
    pure $ FreshMeta r desc (ActorMeta ACitizen av, a)

  Let r av desc t a -> do
    (desc, av, ovs) <- during FreshMetaElaboration $ do
      syndecls <- gets (Map.keys . syntaxCats)
      desc <- ssyntaxdesc syndecls desc
      av <- isFresh av
      ovs <- asks objVars
      pure (desc, av, ovs)
    t <- stm (LetBound (getRange t)) desc t
    a <- local (declare (Used av) (ActVar IsNotSubject (Known desc) ovs)) $ sact a
    pure (Let r (ActorMeta ACitizen av) desc t a)

  Under r (Scope v@(Hide x) a) -> do
    during UnderElaboration $ () <$ isFresh x
    a <- local (declareObjVar (getVariable x, Unknown)) $ sact a
    pure $ Under r (Scope v a)

  Match r rsc cls -> do
    (esc, sc) <- during (MatchScrutineeElaboration rsc) $ sscrutinee rsc
    chs <- get
    (clsts, cov) <- traverse (sclause esc) cls `runStateT` [escrutinee esc]
    unless (null cov) $ do
      table <- gets syntaxCats
      let examples = fromList cov >>= missing table
      raiseWarning $ MissingClauses r examples
    let (cls, sts) = unzip clsts
    let (chst, avst) = unzip $ catMaybes sts
    during (MatchElaboration rsc) $ do
      consistentCommunication  r chst
      consistentScrutinisation r avst
    pure $ Match r sc cls

  Push r stk (p, (), t) a -> do
    (stk, stkTy) <- isContextStack stk

    p <- resolve p >>= \case
      Just (Right (cat, i)) -> i <$ compatibleInfos (getRange p) cat (Known $ keyDesc stkTy)
      Just (Left k) -> throwError $ NotAValidPatternVariable r p k
      _ -> throwError $ OutOfScope (getRange p) p
    t <- during (PushTermElaboration t) $ stm (Pushed r) (valueDesc stkTy) t
    a <- sact a
    pure $ Push r stk (p, valueDesc stkTy, t) a

  Fail r fmt -> Fail r <$> sformat fmt <* tell (All False)
  Print r fmt a -> Print r <$> sformat fmt <*> sact a
  Break r fmt a -> Break r <$> sformat fmt <*> sact a
  Note r a -> Note r <$> sact a

sformat :: [Format Directive Debug Raw] -> Elab [Format Directive Debug ACTm]
sformat fmt = do
  desc <- fromInfo unknown Unknown
  traverse (traverse $ stm DontLog desc) fmt

consistentCommunication :: Range -> [ChannelStates] -> Elab ()
consistentCommunication r sts =
 case List.groupBy ((==) `on` fmap (\ (_,_,x) -> x)) sts of
   [] -> tell (All False) -- all branches are doomed, we don't care
   [(c:_)] -> modify (\ r -> r { channelStates = c })
   _ -> throwError (InconsistentCommunication r)

consistentScrutinisation :: Range -> [ActvarStates] -> Elab ()
consistentScrutinisation r sts = do
  ds <- asks declarations
  let subjects = flip foldMap ds $ \case
        (nm, ActVar IsSubject{} _) -> Set.singleton nm
        _ -> Set.empty
  let check = List.groupBy cmp (flip Map.restrictKeys subjects <$> sts)
  unless (null check) $
    modify (\ r -> r { actvarStates = foldr (Map.unionWith (<>)) Map.empty sts })
  case check of
    _:_:_ -> raiseWarning (InconsistentScrutinisation r)
    _ -> pure ()

  where
    cmp x y = let
      x' = fmap (,B0) x
      y' = fmap (B0,) y
      xy = Map.unionWith (<>) x' y'
      in flip all xy $ \ (xz, yz) -> wasScrutinised xz == wasScrutinised yz

sbranch :: Range -> Decls -> CActor -> Elab (AActor, Maybe (ChannelStates, ActvarStates))
sbranch r ds ra = do
  chs <- gets channelStates
  (a, All b) <- censor (const (All True)) $ listen $ sact ra
    -- make sure that the *newly bound* subject variables have been scrutinised
  forM ds $ \case -- HACK
    (nm, ActVar isSub _) ->
      unlessM (checkScrutinised (Used nm)) $
--        whenJust me $ \ _ -> -- HACK: do not complain about dead branches
          case isSub of
            IsSubject{} -> raiseWarning (PatternSubjectNotScrutinised r nm)
            _ -> pure ()
    _ -> pure ()

  st <- get
  unless b $ unless (chs == channelStates st) $
    throwError (DoomedBranchCommunicated (getRange ra) ra)
  put (st { channelStates = chs })
  pure (a, ((,) <$> channelStates <*> actvarStates) st  <$ guard b )

sclause :: EScrutinee -> (RawP, CActor) ->
           StateT [SyntaxDesc] Elab ((Pat, AActor), Maybe (ChannelStates, ActvarStates))
sclause esc (rp, a) = do
  ds0 <- asks declarations
  avs <- lift $ gets actvarStates
  (mr, p, ds, hs) <- lift $ during (MatchBranchElaboration rp) $ spat esc rp
  let pats = takez ds (length ds - length ds0)
  coverageCheckClause rp p
  (a, me) <- lift $ during (MatchBranchElaboration rp) $
               local (setDecls ds . setHints hs) $ sbranch (getRange rp) pats a
  lift $ modify (\ st -> st { actvarStates = avs })
  -- make sure no catchall on subject pattern, except in dead branches
  whenJust (me *> mr) (lift . raiseWarning . UnderscoreOnSubject)
  pure ((p, a), me)

coverageCheckClause :: RawP -> Pat -> StateT [SyntaxDesc] Elab ()
coverageCheckClause rp p = do
  leftovers <- get
  table <- lift $ gets syntaxCats
  leftovers <- lift $ case combine $ map (\ d -> (d, shrinkBy table d p)) leftovers of
    Covering -> pure []
    AlreadyCovered -> do
      unless (isCatchall p) $
        -- For now we don't complain about catchalls because they may
        -- catching variables.
        raiseWarning (UnreachableClause (getRange rp) rp)
      pure leftovers
    PartiallyCovering _ ps -> pure ps
  put leftovers


sprotocol :: CProtocol -> Elab AProtocol
sprotocol p = during (ProtocolElaboration p) $ do
  syndecls <- gets (Map.keys . syntaxCats)
  Protocol <$> traverse (bitraverse (traverse $ ssyntaxdesc syndecls) ssemanticsdesc) (getProtocol p)

scontextstack :: CContextStack -> Elab AContextStack
scontextstack (ContextStack key val) = do
  syndecls <- gets (Map.keys . syntaxCats)
  key <- ssyntaxdesc syndecls key
  val <- ssyntaxdesc syndecls val
  pure (ContextStack key val)
