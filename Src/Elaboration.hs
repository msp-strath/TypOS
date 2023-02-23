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
    ( SyntaxCat,
      SyntaxDesc, syntaxDesc)
import Thin
import Utils
import Info
import Machine.Matching

import Elaboration.Monad
import Term.Base
import qualified Term.Base as Term
import Term.Substitution
import Pattern as P hiding (match)
import Location
import Data.List.NonEmpty (fromList)
import Pattern.Coverage (Covering'(..), combine, shrinkBy, missing)
import Control.Applicative ((<|>))
import Operator
import Operator.Eval
import Semantics
import Debug.Trace (traceShow)

type CPattern = PATTERN Concrete
type APattern = PATTERN Abstract

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
      Just (ADeclaration (ActVar (IsSubject {}) _)) -> pure . Just $ getVariable v
      _ -> Nothing <$ raiseWarning tm (SentSubjectNotASubjectVar tm)
    Sbst r sg x -> do
      case isInvertible localVars sg of
        Nothing -> Nothing <$ raiseWarning tm (SentSubjectNotASubjectVar tm)
        Just localVars -> go localVars x
    _ -> Nothing <$ raiseWarning tm (SentSubjectNotASubjectVar tm)
  isInvertible :: Bwd String -> Bwd Assign -> Maybe (Bwd String)
  isInvertible = undefined
  {-
  isInvertible lvz B0 = pure lvz
  isInvertible (lvz :< w) (sz :< Keep _ v) | getVariable v == w
    = (:< w) <$> isInvertible lvz sz
  isInvertible (lvz :< w) (sz :< Drop _ v) | getVariable v == w
    = isInvertible lvz sz
  isInvertible lvz (sz :< Assign _ v (Var _ w)) | Just (lz, x, ls) <- focus (getVariable w) lvz
    = (:< getVariable v) <$> isInvertible (lz <>< ls) sz
  isInvertible _ _ = Nothing
-}

escrutinee :: EScrutinee -> ASemanticsDesc
escrutinee = \case
  Pair _ p q -> Semantics.contract (Semantics.VCons (escrutinee p) (escrutinee q))
  SubjectVar _ desc -> desc
  Lookup _ desc _ -> desc
  -- TODO : do we need to pass in the scope?
  Compare _ t1 t2 -> Semantics.contract (Semantics.VEnumOrTag 0 ["LT", "EQ", "GT"] [])
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
  whenJust res $ \ _ -> throwComplaint x (VariableShadowing x)
  pure (getVariable x)

spassport :: Usage -> IsSubject -> Passport
spassport u IsSubject{} | isBeingScrutinised u = ASubject
spassport _ _ = ACitizen

smeta :: Usage
      -> ActorMeta {- eps -}
      -> ACTSbst {- delta -} {- gamma -}
      -> Telescopic ASemanticsDesc {- delta -} {- eps -}
      -> Elab ({- T :: -} ASemanticsDesc {- gamma -}, ACTm {- gamma -} {- T -})
smeta usage am sg (Stop desc) = pure (desc //^ sg, am $: sg)
smeta usage am sg (Tele desc (Scope (Hide x) tel)) = do
  t <- stm usage (desc //^ sg) (Var unknown $ Variable unknown x)
  smeta usage am (sbstT sg ((Hide x :=) $^ t)) tel

svar :: Usage
     -> Maybe ASemanticsDesc
     -> Variable
     -> Elab (IsSubject, ASemanticsDesc, ACTm)
svar usage mdesc' x = do
  let r = getRange x
  ovs <- asks objVars
  res <- resolve x
  case res of
    Just (ADeclaration k) -> case k of
      ActVar isSub (sc :=> desc) -> do
        logUsage (getVariable x) usage
        let tel = discharge sc desc
        let am  = ActorMeta (spassport usage isSub) (getVariable x)
        (desc, tm) <- smeta usage am (sbst0 $ scopeSize ovs) tel
        desc <- fmap (fromMaybe desc) $ flip traverse mdesc' $ \desc' -> do
          i <- compatibleInfos r (Known desc') (Known desc)
          fromInfo r i -- cannot possibly fail
          pure desc
        pure (isSub, desc, tm)
      _ -> throwComplaint x (NotAValidTermVariable x k)
    Just (AnObjVar desc i) -> do
      desc <- fmap (fromMaybe desc) $ flip traverse mdesc' $ \desc' -> do
        i <- compatibleInfos r (Known desc') (Known desc)
        fromInfo r i -- cannot possibly fail
      pure (IsNotSubject, desc, var i (scopeSize ovs))
    Just (AMacro t) -> do
      (desc, t) <- case mdesc' of
         Nothing -> itm usage t
         Just desc -> (desc,) <$> stm usage desc t
      pure (IsNotSubject, desc, t)
    Nothing -> throwComplaint x (OutOfScope x)

spop :: Range -> Elab (ObjVars, (Variable, ASemanticsDesc))
spop r = do
  ovs <- asks objVars
  case getObjVars ovs of
    B0 -> throwComplaint r EmptyContext
    (xz :< ObjVar x cat) -> pure (ObjVars xz, (Variable r x, cat))

ssyntaxdesc :: [SyntaxCat] -> Raw -> Elab SyntaxDesc
ssyntaxdesc syndecls syn = do
  let desc = catToDesc "Syntax"
  syn <- withSyntax (syntaxDesc syndecls) $ stm DontLog desc syn
  case isMetaFree syn of
    Nothing -> error "Impossible in ssyntaxdesc" -- this should be impossible, since parsed in empty context
    Just syn0 -> pure syn0

smacro :: Bwd String -> Raw -> Elab ()
smacro xz (Var r v) = do
  unless (getVariable v `elem` xz) $ do
    x <- resolve v
    whenNothing x $ throwComplaint r (OutOfScope v)
smacro xz (At r a) = pure ()
smacro xz (Cons r t u) = do
  smacro xz t
  smacro xz u
smacro xz (Lam r (Scope (Hide x) sc)) = do
  xz <- case x of
    Unused -> pure xz
    Used x -> do x <- isFresh x
                 pure (xz :< x)
  smacro xz sc
smacro xz (Sbst r sg t) = do
  xz <- smacros xz (sg <>> [])
  smacro xz t
smacro xz (Op r obj opps) = do
  smacro xz obj
  smacro xz opps
smacro xz (Guarded r t) = smacro xz t

smacros :: Bwd String -> [Assign] -> Elab (Bwd String)
smacros xz [] = pure xz
smacros xz (Assign r x t : asss) = do
  x <- isFresh x
  smacro xz t
  smacros (xz :< x) asss

ssbst :: [Assign] -> Elab Macros
ssbst [] = asks macros
ssbst (Assign r x t : asss) = do
  x <- isFresh x
  smacro B0 t
  local (declareMacro (x, t)) $ ssbst asss



{-usage B0 = do
    ovs <- asks objVars
    pure (sbstI (scopeSize ovs), ovs)
ssbst usage (sg :< sgc) = case sgc of
    Assign r v t -> do
      (sg, ovs) <- ssbst usage sg
      -- ovs better be a valid scope (without Drop, we know it will be)
      local (setObjVars' ovs) $ do
        v <- isFresh v
        (desc, t) <- itm usage t
        pure (sbstT sg ((Hide v :=) $^ t), ovs <: ObjVar v desc)
    _ -> undefined
-}

{-
ssbst :: Usage -> Bwd Assign -> Elab (ACTSbst, ObjVars)
ssbst usage B0 = do
    ovs <- asks objVars
    pure (sbstI (scopeSize ovs), ovs)
ssbst usage (sg :< sgc) = case sgc of
    Keep r v -> do
      (xz, (w, cat)) <- spop r
      when (v /= w) $ throwComplaint r (NotTopVariable v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst usage sg)
      pure (sbstW sg (ones 1), ovs <: ObjVar (getVariable w) cat)
    -- TODO : worry about dropped things ocurring in types
    Drop r v -> do
      (xz, (w, cat)) <- spop r
      when (v /= w) $ throwComplaint r (NotTopVariable v w)
      (sg, ovs) <- local (setObjVars xz) (ssbst usage sg)
      pure (weak sg, ovs)
    Assign r v t -> do
      (sg, ovs) <- ssbst usage sg
      local (setObjVars ovs) $ do
        (desc, t) <- itm usage t
        v <- isFresh v
        pure (sbstT sg ((Hide v :=) $^ t), ovs <: ObjVar v (Known desc))
-}

sth :: Restriction -> (Bwd Variable, ThDirective) -> Elab Th
sth (Restriction ovs th) (xz, b) = do
  let th = which (`elem` (getVariable <$> xz)) ovs
  pure $ case b of
    ThKeep -> th
    ThDrop -> comp th

stms :: Usage -> [ASemanticsDesc] -> Raw -> Elab ACTm
stms usage [] (At r "") = atom "" <$> asks (scopeSize . objVars)
stms usage [] (At r a) = throwComplaint r (ExpectedNilGot a)
stms usage [] t = throwComplaint t (ExpectedANilGot t)
stms usage (d:ds) (Cons r p q) = (%) <$> stm usage d p <*> stms usage ds q
stms usage _ t = throwComplaint t (ExpectedAConsGot t)

sscrutinee :: CScrutinee -> Elab (EScrutinee, AScrutinee)
sscrutinee (SubjectVar r v) = do
  -- TODO: shouldn't this svar return a syntax desc?
  -- We're in subject analysis mode
  (isSub, desc, actm) <- svar (Scrutinised r) Nothing v
  case (isSub, actm) of
    (IsSubject{}, CdB (m :$ sg) _) -> pure (SubjectVar r desc, SubjectVar r actm)
    _ -> throwComplaint r (NotAValidSubjectVar v)
sscrutinee (Pair r sc1 sc2) = do
  (esc1, asc1) <- sscrutinee sc1
  (esc2, asc2) <- sscrutinee sc2
  pure (Pair r esc1 esc2, Pair r asc1 asc2)
sscrutinee (Lookup r stk v) = do
  (stk, stkTy) <- isContextStack stk
  t <- during (LookupVarElaboration v) $ do
    desc <- asSemantics (keyDesc stkTy)
    (isSub, desc, t) <- svar (LookedUp r) (Just desc) v
    pure t
  let vdesc = valueDesc stkTy
      desc = Semantics.contract (VEnumOrTag (scope vdesc) ["Nothing"] [("Just", [vdesc])])
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


satom :: String -> Elab ACTm
satom at = atom at <$> asks (scopeSize . objVars)

sty :: CSemanticsDesc -> Elab ASemanticsDesc
sty t = do
  sem <- satom "Semantics"
  stm DontLog sem t

ssot :: SOT 'Concrete -> Elab ASOT
ssot ([], ty) = (:=>) <$> asks objVars <*> sty ty
ssot ((desc, x) : xs, ty) = do
  desc <- sty desc
  x <- isFresh x
  local (declareObjVar (x, desc)) $ ssot (xs, ty)

sparamdescs :: [(Maybe Variable, ([(Raw, Variable)], Raw))]
            -> Elab ([(Maybe ActorMeta, ASOT)], Decls)
sparamdescs [] = ([],) <$> asks declarations
sparamdescs ((mx , sot):ps) = do
  sot <- ssot sot
  (mx, binder) <- case mx of
    Nothing -> pure (Nothing, Unused)
    Just x -> do
      x <- isFresh x
      pure (Just (ActorMeta ACitizen x) , Used x)
  (ps, ds) <- local (declare binder (ActVar IsNotSubject sot)) $ sparamdescs ps
  pure ((mx , sot):ps, ds)

spatSemantics0 :: ASemanticsDesc -> CPattern -> Elab (APattern, Decls, ACTm)
spatSemantics0 desc p = do
  ovs <- asks objVars
  spatSemantics desc (initRestriction ovs) p

data ConsDesc
  = ConsCell ASemanticsDesc ASemanticsDesc
  | ConsEnum [(String, [ASemanticsDesc])]
  | ConsUniverse

spatSemantics :: ASemanticsDesc -> Restriction -> CPattern ->
                 Elab (APattern, Decls, ACTm)
spatSemantics desc rest (Irrefutable r p) = do
  raiseWarning r (IgnoredIrrefutable p) -- TODO
  spatSemantics desc rest p
spatSemantics desc rest (AsP r v p) = do
  v <- isFresh v
  ds <- asks declarations
  (ovs, asot) <- thickenedASOT r (restriction rest) desc
  (p, ds, t) <-
    local (setDecls (ds :< (v, ActVar IsNotSubject asot))) $ spatSemantics desc rest p
  pure (AT (ActorMeta ACitizen v) p, ds, t)
spatSemantics desc rest (ThP r ph p) = do
  ph <- sth rest ph
  (p, ds, t) <- spatSemantics desc (ph ^? rest) p
  pure (p *^ ph, ds, t *^ ph)
spatSemantics desc rest (UnderscoreP r) = do
  ds <- asks declarations
  let hack = Variable r ("_" ++ show (length ds))
  spatSemantics desc rest (VarP r hack)
spatSemantics desc rest (VarP r v) = during (PatternVariableElaboration v) $ do
  ds <- asks declarations
  res <- resolve v
  let th = restriction rest
  let scp = weeEnd th
  case res of
    Just (AnObjVar desc' i) -> do
      i <- case thickx th i of -- TODO: do we need to check whether desc' is thickenable?
        Nothing -> throwComplaint r (OutOfScope v)
        Just i -> pure i
      compatibleInfos (getRange v) (Known desc) (Known desc')
      pure (VP i, ds, var i scp)
    Just mk -> throwComplaint r (NotAValidPatternVariable v mk)
    Nothing -> do
      (ovs, asot) <- thickenedASOT r th desc
      v <- pure (getVariable v)
      let pat = MP (ActorMeta ACitizen v) (ones scp)
      pure (pat, ds :< (v, ActVar IsNotSubject asot), ActorMeta ACitizen v $: sbstI scp)
spatSemantics desc rest rp = do
  table <- gets syntaxCats
  dat <- asks headUpData
  ds <- asks declarations
  case Semantics.expand table dat desc of
    Nothing -> throwComplaint rp (InvalidSemanticsDesc desc)
    Just vdesc -> case rp of
      AtP r a -> do
        case vdesc of
          VAtom _ -> pure ()
          VAtomBar _ as -> when (a `elem` as) $ throwComplaint r (GotBarredAtom a as)
          VNil _ -> unless (a == "") $ throwComplaint r (ExpectedNilGot a)
          VNilOrCons{} -> unless (a == "") $ throwComplaint r (ExpectedNilGot a)
          VEnumOrTag sc es _ -> unless (a `elem` es) $ throwComplaint r (ExpectedEnumGot es a)
          VWildcard sc -> pure ()
          VUniverse _ -> unless (a `elem` ("Semantics" : Map.keys table)) $ throwComplaint r (ExpectedASemanticsGot (At r a))
          _ -> throwComplaint r (SyntaxPError desc rp)
        pure (AP a, ds, atom a (weeEnd (restriction rest)))
      ConsP r p1 p2 -> do
        -- take vdesc apart and decide what needs to be checked
        -- Left (d1, d2): usual cons cell
        -- Right ds     : enumeration (ds :: [(String, [Desc])])
        descs <- case vdesc of
          VNilOrCons d1 d2 -> pure (ConsCell d1 d2)
          VCons d1 d2 -> pure (ConsCell d1 d2)
          VWildcard _ -> pure (ConsCell desc desc)
          VEnumOrTag _ _ ds -> pure (ConsEnum ds)
          VUniverse _ -> pure ConsUniverse
          _ -> throwComplaint r (SyntaxPError desc rp)
        case descs of
          ConsCell d1 d2 -> do
            (p1, ds, t1) <- spatSemantics d1 rest p1
            (p2, ds, t2) <- local (setDecls ds) (spatSemantics d2 rest p2)
            pure (PP p1 p2, ds, t1 % t2)
          ConsEnum ds -> case p1 of
            AtP r a -> case lookup a ds of
              Nothing -> throwComplaint r (ExpectedTagGot (fst <$> ds) a)
              Just descs ->  do
                at <- satom "Atom"
                (p1, ds, t1) <- spatSemantics at rest p1
                (p2, ds, t2) <- local (setDecls ds) (spatSemanticss descs rest p2)
                pure (PP p1 p2, ds, t1 % t2)
            _ -> throwComplaint r (SyntaxPError desc rp)
          ConsUniverse -> case (p1 , p2) of
            (AtP _ "Pi", ConsP _ s (ConsP _ (LamP _ (Scope (Hide x) t)) (AtP _ ""))) -> do
              (ps, ds, ts) <- spatSemantics desc rest s
              (pt, ds, tt) <-
                local (setDecls ds) $
                  elabUnder (x, ts) $ do
                    -- TODO: refactor this
                    -- complex interaction between restriction throwing "_" out of scope
                    -- and Discheargeable (via elabUnder) abstracting over it on the way out
                    (pt, ds, tt) <- spatSemantics (weak desc) (extend rest (getVariable <$> x)) t
                    (pt, tt) <- case x of
                      Unused -> do sc <- asks (scopeSize . objVars)
                                   pure (pt *^ (ones sc -? False), weak tt)
                      Used _ -> pure (pt, tt)
                    pure (pt, ds, tt)
              pure (PP (AP "Pi") (PP ps (PP pt (AP "")))
                   , ds
                   , "Pi" #%+ [ts,tt])
            _ -> throwComplaint r (ExpectedASemanticsPGot rp)

      LamP r (Scope v@(Hide x) p) -> do
        (s, desc) <- case vdesc of
          VWildcard _ -> pure (desc, weak desc)
          VBind cat desc -> pure (Semantics.catToDesc cat, weak desc)
          VPi s (y, t) -> pure (s, t)
          _ -> throwComplaint r (SyntaxPError desc rp)
        elabUnder (x, s) $ do
          (pt, ds, tt) <- spatSemantics desc (extend rest (getVariable <$> x)) p
          sc <- asks (scopeSize . objVars)
          pure (pt *^ (ones sc -? False), ds, weak tt)

spatSemanticss :: [ASemanticsDesc]
               -> Restriction
               -> RawP
               -> Elab (Pat, Decls, ACTm)
spatSemanticss [] rest (AtP r "") = (AP "",, atom "" (weeEnd (restriction rest))) <$> asks declarations
spatSemanticss [] rest (AtP r a) = throwComplaint r (ExpectedNilGot a)
spatSemanticss [] rest t = throwComplaint t (ExpectedANilPGot t)
spatSemanticss (d:ds) rest (ConsP r p ps) = do
  (p, decls, t) <- spatSemantics d rest p
  (ps, decls, ts) <- local (setDecls decls) $ spatSemanticss ds rest ps
  pure (PP p ps, decls, t % ts)
spatSemanticss _ rest t = throwComplaint t (ExpectedAConsPGot t)

isList :: Raw -> Elab [Raw]
isList (At r "") = pure []
isList (At r a) = throwComplaint r (ExpectedNilGot a)
isList (Cons r p q) = (p:) <$> isList q

isList t = throwComplaint t (ExpectedAConsGot t)

-- Input: fully applied operator ready to operate
-- Output: (abstract operator, raw parameters)
sop :: Raw -> Elab (AAnOperator, [Raw])
sop (At ra a) = do
  op <- isOperator ra a
  pure (op, [])
sop (Cons rp (At ra a) ps) = do
  op <- isOperator ra a
  es <- isList ps
  pure (op, es)
sop ro = throwComplaint ro (ExpectedAnOperator ro)

-- e.g.  (p : ['Sig S \x.T]) -'snd
--       ['MkSig a b] : ['Sig A \y.B]
-- Then we want an environment extended by: (S = A, \x.T = \y.B, p = ['MkSig a b])
matchObjType :: Range -> (Maybe ActorMeta, Pat) -> (ASemanticsDesc, ACTm) -> Elab (HeadUpData' ActorMeta)
matchObjType r (mb , oty) (obDesc, ob) = do
    dat <- asks headUpData
    let hnf = headUp dat
    env <- case snd $ match hnf initMatching (Problem B0 oty obDesc) of
      Left e -> throwComplaint r $ InferredDescMismatch
      Right m -> pure $ matchingToEnv m (huEnv dat)
    env <- case mb of
      Nothing -> pure env
      Just v  -> pure $ newActorVar v (localScope env <>> [], ob) env
    pure dat{huEnv = env}

itm :: Usage -> Raw -> Elab (ASemanticsDesc, ACTm)
itm usage (Var r v) = do
  (_, desc, v) <- svar usage Nothing v
  pure (desc, v)
-- rob -rop
itm usage (Op r rob rop) = do
  (obDesc, ob) <- itm usage rob
  (AnOperator{..}, rps) <- sop rop
  dat <- matchObjType r objDesc (obDesc, ob)
  local (setHeadUpData dat) $ do
    (desc, ps) <- itms r usage paramsDesc rps retDesc
    pure (desc, ob -% (getOperator opName, ps))
-- TODO?: annotated terms?
itm _ t = throwComplaint t $ DontKnowHowToInferDesc t

itms :: Range -> Usage
        -- Parameters types e.g. (_ : 'Nat\n. {m = n}p\ih. {m = ['Succ n]}p)
     -> [(Maybe ActorMeta, ASOT)]
        -- Raw parameters
     -> [Raw]
        -- Return type
     -> ASemanticsDesc
        --
     -> Elab (ASemanticsDesc -- Instantiated return type
             , [ACTm])       -- Elaborated parameters
itms r usage [] [] rdesc = (, []) <$> instantiateDesc r rdesc
itms r usage ((binder, sot):bs) (rp:rps) rdesc = do
  (ovs :=> desc) <- instantiateSOT (getRange rp) sot
  (p, dat) <- sparam usage binder B0 (discharge ovs desc) rp
  local (setHeadUpData dat) $
    fmap (p:) <$> itms r usage bs rps rdesc
itms r usage bs rps rdesc = throwComplaint r $ ArityMismatchInOperator

sparam :: Usage
       -> Maybe ActorMeta -- Name of parameter
       -> Bwd String      -- Names of formal parameters of the parameter
       -> Telescopic ASemanticsDesc -- Type of the parameter
       -> Raw             -- Raw term naming the actual parameters
       -> Elab (ACTm, HeadUpData' ActorMeta) -- Elaborated term,
                                             -- headupdata with the parameter defined
sparam usage binder namez (Stop pdesc) rp = do
  p <- stm usage pdesc rp
  dat <- do
    dat <- asks headUpData
    pure $ case binder of
      Nothing -> dat
      Just v  ->
        let env = huEnv dat
            env' = newActorVar v (namez <>> [], p) env
        in dat {huEnv = env'}
  pure (p, dat)
sparam usage binder namez (Tele desc (Scope (Hide name) tele)) (Lam r (Scope (Hide x) rp)) =
  elabUnder (x, desc) $ sparam usage binder (namez :< name) tele rp
sparam _ _ _ _ rp = throwComplaint rp $ ExpectedParameterBinding rp

instantiateSOT :: Range -> ASOT -> Elab ASOT
instantiateSOT r (ovs :=> desc)
  = (:=>) <$> traverse (instantiateDesc r) ovs <*> instantiateDesc r desc

instantiateDesc :: Range -> ASemanticsDesc -> Elab ASemanticsDesc
instantiateDesc r desc = do
  dat  <- asks headUpData
  -- The object acted upon and the parameters appearing before the
  -- one currently being elaborated need to be substituted into the desc
  case mangleActors (huOptions dat) (huEnv dat) desc of
    Nothing -> throwComplaint r $ SchematicVariableNotInstantiated
    Just v  -> pure v


{-
sp is only for Concrete p to Abstract p

sasot :: Range -> ASOT -> Elab ASemanticsDesc
sasot r (objVars :=> desc) = do
  dat  <- asks headUpData
  -- The object acted upon and the parameters appearing before the
  -- one currently being elaborated need to be substituted into the SOT
  case mangleActors (huOptions dat) (huEnv dat) desc of
    Nothing -> throwComplaint r $ SchematicVariableNotInstantiated r
    Just v  -> pure v -- TODO: foldr (\ (x,t) v => ['Bind t \x.v]) id v
-}

stm :: Usage -> ASemanticsDesc -> Raw -> Elab ACTm
stm usage desc (Var r v) = during (TermVariableElaboration v) $ do
  table <- gets syntaxCats
  (_, _, t) <- svar usage (Just desc) v
  pure t
stm usage desc (Sbst r sg t) = do
    ms <- during (SubstitutionElaboration sg) $ ssbst (sg <>> [])
    local (setMacros ms) (stm usage desc t)
stm usage desc rt = do
  table <- gets syntaxCats
  dat <- asks headUpData
  case Semantics.expand table dat desc of
    Nothing -> throwComplaint rt (InvalidSemanticsDesc desc)
    Just vdesc -> case rt of
      At r a -> do
        case vdesc of
          VAtom _ -> pure ()
          VAtomBar _ as -> when (a `elem` as) $ throwComplaint r (GotBarredAtom a as)
          VNil _ -> unless (a == "") $ throwComplaint r (ExpectedNilGot a)
          VNilOrCons{} -> unless (a == "") $ throwComplaint r (ExpectedNilGot a)
          VEnumOrTag _ es _ -> unless (a `elem` es) $ throwComplaint r (ExpectedEnumGot es a)
          VWildcard _ -> pure ()
          VUniverse _ -> unless (a `elem` ("Semantics" : Map.keys table)) $ throwComplaint r (ExpectedASemanticsGot rt)
             --  TODO we're probably missing semantics here
          _ -> throwComplaint r (SemanticsError desc rt)
        satom a
      Cons r p q -> case vdesc of
        VNilOrCons d1 d2 -> (%) <$> stm usage d1 p <*> stm usage d2 q
        VCons d1 d2 -> (%) <$> stm usage d1 p <*> stm usage d2 q
        VWildcard _ -> (%) <$> stm usage desc p <*> stm usage desc q
        VEnumOrTag _ _ ds -> case p of
          At r a -> case lookup a ds of
            Nothing -> throwComplaint r (ExpectedTagGot (fst <$> ds) a)
            Just descs -> (%) <$> stm usage (atom "Atom" 0) p <*> stms usage descs q
          _ -> throwComplaint r (SyntaxError desc rt)
        VUniverse _ -> case (p , q) of
          (At _ "Pi", Cons _ s (Cons _ (Lam _ (Scope (Hide x) t)) (At _ ""))) -> do
            s <- sty s
            t <- elabUnder (x, s) $ sty t
            pure ("Pi" #%+ [s, t])
          _ -> throwComplaint r (ExpectedASemanticsGot rt)
        _ -> throwComplaint r (SyntaxError desc rt)
      Lam r (Scope (Hide x) sc) -> do
        (s, desc) <- case vdesc of
          VWildcard i -> pure (desc, weak desc)
          VBind cat desc -> pure (catToDesc cat, weak desc)
          VPi s (y, t) -> pure (s, t)
          _ -> throwComplaint r (SyntaxError desc rt)
        elabUnder (x, s) $ stm usage desc sc
      Op{} -> do
        (tdesc, t) <- itm usage rt
        compatibleInfos (getRange rt) (Known tdesc) (Known desc)
        pure t

elabUnder :: Show a => Dischargeable a => (Binder Variable, ASemanticsDesc) -> Elab a -> Elab a
elabUnder (x, desc) ma = do
  x <- case x of
        Used x -> isFresh x
        Unused -> pure "_"
  (x \\) {-. (\ x -> traceShow x x) -} <$> local (declareObjVar (x, desc)) ma

spats :: IsSubject -> [ASemanticsDesc] -> Restriction -> RawP -> Elab (Maybe Range, Pat, Decls, Hints)
spats _ [] rest (AtP r "") = (Nothing, AP "",,) <$> asks declarations <*> asks binderHints
spats _ [] rest (AtP r a) = throwComplaint r (ExpectedNilGot a)
spats _ [] rest t = throwComplaint t (ExpectedANilPGot t)
spats isSub (d:ds) rest (ConsP r p q) = do
  (mr1, p, decls, hints) <- spatBase isSub d rest p
  (mr2, q, decls, hints) <- local (setDecls decls . setHints hints) $ spats isSub ds rest q
  pure (mr1 <|> mr2, PP p q, decls, hints)
spats _ _ rest t = throwComplaint t (ExpectedAConsPGot t)

-- Inputs:
--   0. Elaborated scrutinee -- description of how the scrutinee we are
--   matching on was formed
--   1. Pair of local variables and thinning describing what we are
--   allowed to depend on
--   2. Raw pattern to elaborate
-- Returns:
--   0. Whether a subject pattern was thrown away
--   1. Elaborated pattern
--   2. Bound variables (together with their syntactic categories)
--   3. Binder hints introduced by \x. patterns
spat :: EScrutinee -> Restriction -> RawP -> Elab (Maybe Range, Pat, Decls, Hints)
spat esc rest rp@(AsP r v p) = do
  unless (isSubjectFree esc) $
    throwComplaint r (AsPatternCannotHaveSubjects rp)
  let desc = escrutinee esc
  v <- isFresh v
  ds <- asks declarations
  (ovs, asot) <- thickenedASOT r (restriction rest) desc
  (mr, p, ds, hs) <- local (setDecls (ds :< (v, ActVar IsNotSubject asot))) $ spat esc rest p
  pure (mr, AT (ActorMeta ACitizen v) p, ds, hs)
spat esc rest p@VarP{} = spatBase (Pattern <$ isSubject esc) (escrutinee esc) rest p
spat esc rest (ThP r ph p) = do
  ph <- sth rest ph
  (mr, p, ds, hs) <- spat esc (ph ^? rest) p
  pure (mr, p *^ ph, ds, hs)
spat esc rest p@(UnderscoreP r) = do
  (_, p, ds, hs) <- spatBase (Pattern <$ isSubject esc) (escrutinee esc) rest p
  let mr = r <$ guard (not (isSubjectFree esc))
  pure (mr, p, ds, hs)
spat esc@(Pair r esc1 esc2) rest rp = case rp of
  ConsP r p q -> do
    (mr1, p, ds, hs) <- spat esc1 rest p
    (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spat esc2 rest q)
    pure (mr1 <|> mr2, PP p q, ds, hs)
  _ -> throwComplaint rp (SyntaxPError (escrutinee esc) rp)
spat (SubjectVar r desc) rest rp = spatBase (IsSubject Pattern) desc rest rp
spat esc@(Lookup _ _ av) rest rp@(ConsP r (AtP _ "Just") (ConsP _ _ (AtP _ ""))) = do
  logUsage av (SuccessfullyLookedUp r)
  spatBase IsNotSubject (escrutinee esc) rest rp
spat esc@(Lookup _ _ av) rest rp = spatBase IsNotSubject (escrutinee esc) rest rp
spat esc@(Compare{}) rest rp = spatBase IsNotSubject (escrutinee esc) rest rp
spat esc@(Term{}) rest rp = spatBase IsNotSubject (escrutinee esc) rest rp

thickenedASOT :: Range -> Th -> ASemanticsDesc -> Elab (ObjVars, ASOT)
thickenedASOT r th desc = do
  ovs <- asks objVars
  ovs <- case thickenObjVars th ovs of
    Nothing -> throwComplaint r (NotAValidContextRestriction th ovs)
    Just ovs -> pure ovs
  desc <- case thickenCdB th desc of
    Nothing -> throwComplaint r (NotAValidDescriptionRestriction th desc)
    Just desc -> pure desc
  pure (ovs, ovs :=> desc)

spatBase :: IsSubject -> ASemanticsDesc -> Restriction ->  RawP -> Elab (Maybe Range, Pat, Decls, Hints)
spatBase isSub desc rest rp@(AsP r v p) = do
  unless (isSub == IsNotSubject) $
    throwComplaint r (AsPatternCannotHaveSubjects rp)
  v <- isFresh v
  ds <- asks declarations
  (ovs, asot) <- thickenedASOT r (restriction rest) desc
  (mr, p, ds, hs) <- local (setDecls (ds :< (v, ActVar isSub asot))) $ spatBase isSub desc rest p
  pure (mr, AT (ActorMeta ACitizen v) p, ds, hs)
spatBase isSub desc rest (ThP r ph p) = do
  ph <- sth rest ph
  (mr, p, ds, hs) <- spatBase isSub desc (ph ^? rest) p
  pure (mr, p *^ ph, ds, hs)
spatBase isSub desc rest (VarP r v) = during (PatternVariableElaboration v) $ do
  ds <- asks declarations
  hs <- asks binderHints
  res <- resolve v
  let th = restriction rest
  case res of
    Just (AnObjVar desc' i) -> do
      i <- case thickx th i of -- TODO: do we need to check whether desc' is thickenable?
        Nothing -> throwComplaint r (OutOfScope v)
        Just i -> pure i
      compatibleInfos (getRange v) (Known desc) (Known desc')
      pure (Nothing, VP i, ds, hs)
    Just mk -> throwComplaint r (NotAValidPatternVariable v mk)
    Nothing -> do
      (ovs, asot) <- thickenedASOT r th desc
      v <- pure (getVariable v)
      let pat = MP (ActorMeta (spassport (Scrutinised unknown) isSub) v) (ones $ scopeSize ovs)
      pure (Nothing, pat, ds :< (v, ActVar isSub asot), hs)
spatBase isSub desc rest (UnderscoreP r) = do
  let mr = case isSub of
             IsSubject{} -> Just r
             IsNotSubject -> Nothing
  (mr,HP,,) <$> asks declarations <*> asks binderHints
spatBase isSub desc rest rp = do
  table <- gets syntaxCats
  dat <- asks headUpData
  case Semantics.expand table dat desc of
    Nothing -> throwComplaint rp (InvalidSemanticsDesc desc)
    Just vdesc -> case rp of
      AtP r a -> do
        case vdesc of
          VAtom _ -> pure ()
          VAtomBar _ as -> when (a `elem` as) $ throwComplaint r (GotBarredAtom a as)
          VNil _ -> unless (a == "") $ throwComplaint r (ExpectedNilGot a)
          VNilOrCons{} -> unless (a == "") $ throwComplaint r (ExpectedNilGot a)
          VEnumOrTag sc es _ -> unless (a `elem` es) $ throwComplaint r (ExpectedEnumGot es a)
          VWildcard sc -> pure ()
          _ -> throwComplaint r (SyntaxPError desc rp)
        (Nothing, AP a,,) <$> asks declarations <*> asks binderHints

      ConsP r p q -> case vdesc of
        VNilOrCons d1 d2 -> do
          (mr1, p, ds, hs) <- spatBase isSub d1 rest p
          (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spatBase isSub d2 rest q)
          pure (mr1 <|> mr2, PP p q, ds, hs)
        VCons d1 d2 -> do
          (mr1, p, ds, hs) <- spatBase isSub d1 rest p
          (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spatBase isSub d2 rest q)
          pure (mr1 <|> mr2, PP p q, ds, hs)
        VWildcard _ -> do
          (mr1, p, ds, hs) <- spatBase isSub desc rest p
          (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spatBase isSub desc rest q)
          pure (mr1 <|> mr2, PP p q, ds, hs)
        VEnumOrTag _ _ ds -> case p of
          AtP r a -> case lookup a ds of
            Nothing -> throwComplaint r (ExpectedTagGot (fst <$> ds) a)
            Just descs ->  do
              (mr1, p, ds, hs) <- spatBase isSub (atom "Atom" 0) rest p
              (mr2, q, ds, hs) <- local (setDecls ds . setHints hs) (spats isSub descs rest q)
              pure (mr1 <|> mr2, PP p q, ds, hs)
          _ -> throwComplaint r (SyntaxPError desc rp)
        _ -> throwComplaint r (SyntaxPError desc rp)

      LamP r (Scope v@(Hide x) p) -> do
        (s, desc) <- case vdesc of
          VWildcard _ -> pure (desc, weak desc)
          VBind cat desc -> pure (Semantics.catToDesc cat, weak desc)
          VPi s (y, t) -> pure (s, t)
          _ -> throwComplaint r (SyntaxPError desc rp)

        elabUnder (x, s) $ do
          (mr, p, ds, hs) <- spatBase isSub desc (extend rest (getVariable <$> x)) p
          sc <- asks (scopeSize . objVars)
          pure (mr, p *^ (ones sc -? False), ds, hs)

isObjVar :: Variable -> Elab (ASemanticsDesc, DB)
isObjVar p = resolve p >>= \case
  Just (AnObjVar desc i) -> pure (desc, i)
  Just mk -> throwComplaint p $ NotAValidPatternVariable p mk
  Nothing -> throwComplaint p $ OutOfScope p

isChannel :: Variable -> Elab Channel
isChannel ch = resolve ch >>= \case
  Just (ADeclaration (AChannel sc)) -> pure (Channel $ getVariable ch)
  Just mk -> throwComplaint ch (NotAValidChannel ch mk)
  Nothing -> throwComplaint ch (OutOfScope ch)

isOperator :: Range -> String -> Elab AAnOperator
isOperator r nm = do
  ops <- asks operators
  case Map.lookup nm ops of
    Just res -> pure res
    Nothing -> throwComplaint r (NotAValidOperator nm)

data IsJudgement = IsJudgement
  { judgementExtract :: ExtractMode
  , judgementName :: JudgementName
  , judgementProtocol :: AProtocol
  }

isJudgement :: Variable -> Elab IsJudgement
isJudgement jd = resolve jd >>= \case
  Just (ADeclaration (AJudgement em p)) -> pure (IsJudgement em (getVariable jd) p)
  Just mk -> throwComplaint jd (NotAValidJudgement jd mk)
  Nothing -> throwComplaint jd (OutOfScope jd)

isContextStack :: Variable -> Elab (Stack, AContextStack)
isContextStack stk = resolve stk >>= \case
  Just (ADeclaration (AStack stkTy)) -> pure (Stack (getVariable stk), stkTy)
  Just mk -> throwComplaint stk (NotAValidStack stk mk)
  Nothing -> throwComplaint stk (OutOfScope stk)


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
  unless (pnm `isPrefixOf` nm) $ throwComplaint r (NonLinearChannelUse ch)
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
            throwComplaint r (UnfinishedProtocol ch (Protocol ps))
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
  Just (AnObjVar desc i) -> pure (Known desc)
  Just (ADeclaration (ActVar isSub (ObjVars B0 :=> desc))) -> pure $ Known desc
  _ -> pure Unknown
guessDesc b (Cons _ p q) = do
  dp <- guessDesc False p
  dq <- guessDesc True q
  case (dp, dq) of
    (Known d1, Known d2) -> pure (Known $ Semantics.contract (Semantics.VCons d1 d2))
    _ -> pure Unknown
-- might need better guess for the scope than 0
guessDesc True (At _ "") = pure (Known $ Semantics.contract (Semantics.VNil 0))
guessDesc _ _ = pure Unknown

compatibleChannels :: Range
                   -> (Direction, [AProtocolEntry])
                   -> Ordering
                   -> (Direction, [AProtocolEntry])
                   -> Elab Int
compatibleChannels r (dp, []) dir (dq, []) = pure 0
compatibleChannels r (dp, p@(m, s) : ps) dir (dq, q@(n, t) : qs) = do
  unless (s == t) $ throwComplaint r (IncompatibleSemanticsDescs s t)
  let (cp , cq) = (whatComm m dp, whatComm n dq)
  when (cp == cq) $ throwComplaint r (IncompatibleModes p q)
  case (cp, dir) of
    (RECV, LT) -> throwComplaint r (WrongDirection p dir q)
    (SEND, GT) -> throwComplaint r (WrongDirection p dir q)
    _ -> pure ()
  (+1) <$> compatibleChannels r (dp, ps) dir (dq , qs)
compatibleChannels r (_,ps) _ (_,qs) = throwComplaint r (ProtocolsNotDual (Protocol ps) (Protocol qs))

sirrefutable :: String -> IsSubject -> RawP -> Elab (Binder String, Maybe (CScrutinee, RawP))
sirrefutable nm isSub = \case
  VarP _ v -> (, Nothing) . Used <$> isFresh v
  UnderscoreP _ -> pure (Unused, Nothing)
  p -> do ctxt <- ask
          -- this should be a unique name & is not user-writable
          let r = getRange p
          let av = "&" ++ nm ++ show (scopeSize (objVars ctxt) + length (declarations ctxt))
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
      _ -> throwComplaint r (InvalidSend ch tm)

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
      -- NB: the lintersection takes the ASemanticsDesc into account
      -- Should it? Yes?

      -- AFAWU:
      --   1. sc is a prefix of ovs
      --   2. lintersection sc ovs will return sc (?)
      --   3. thx is the thinning embedding sc back into ovs
      -- => setObjVars would be legitimate because xyz is a valid scope
      let (thx, xyz, thy) = lintersection (getObjVars sc) (getObjVars ovs)
      (*^ thx) <$> local (setObjVars' $ ObjVars xyz) (stm usage desc tm)

    a <- sact a
    pure $ Send r ch gd tm a

  Recv r ch (p, a) -> do
    ch <- isChannel ch

    -- Check the channel is in receiving mode & step it
    (m, cat) <- steppingChannel r ch $ \ dir -> \case
      (m, cat) : p | whatComm m dir == RECV -> pure ((m, cat), p)
      _ -> throwComplaint r (InvalidRecv ch p)

    -- TODO: m contains a SyntaxDesc when it's a subject position
    --       Why do we throw it away? Shouldn't it be stored &
    --       returned when we `svar` with a validation usage?
    -- Should it be stored in the ActVar bound below at GOTO?
    let isSub = case m of
           Subject _ -> IsSubject Parent
           _ -> IsNotSubject

    -- elaborate the (potentially pattern-matching) receive
    (av, pat) <- during (RecvMetaElaboration ch) $ sirrefutable "recv" isSub p

    -- Further actor
    sc <- channelScope ch
    (a, All canwin) <- local (declare av (ActVar isSub (sc :=> cat))) -- GOTO
           $ listen
           $ sact
           $ case pat of
               Nothing -> a
               Just (sc, p) -> Match r sc [(p, a)]

    -- Check we properly scrutinised a subject input
    unlessM (checkScrutinised av) $
      when (isSubjectMode m) $ do
        when canwin $ raiseWarning r (RecvSubjectNotScrutinised ch av)

    pure $ Recv r ch (ActorMeta (spassport (Scrutinised unknown) isSub) <$> av, a)

  Connect r (CConnect ch1 ch2) -> during (ConnectElaboration ch1 ch2) $ do
    ch1 <- isChannel ch1
    ch2 <- isChannel ch2
    p <- steppingChannel r ch1 $ \ dir p -> pure ((dir,p), [])
    q <- steppingChannel r ch2 $ \ dir p -> pure ((dir,p), [])
    sc1 <- channelScope ch1
    sc2 <- channelScope ch2
    (dir, th) <- case (sc1 `thinsTo` sc2, sc2 `thinsTo` sc1) of
      (Just thl, Just thr) -> pure (EQ, thl)
      (Just thl, _) -> pure (LT, thl)
      (_, Just thr) -> pure (GT, thr)
      _ -> throwComplaint r (IncompatibleChannelScopes sc1 sc2)
    steps <- compatibleChannels r p dir q
    pure (aconnect r ch1 th ch2 steps)

  FreshMeta r desc (av, a) -> do
    (desc, av, ovs) <- during FreshMetaElaboration $ do
      syndecls <- gets (Map.keys . syntaxCats)
      desc <- sty desc
      av <- isFresh av
      ovs <- asks objVars
      pure (desc, av, ovs)
    a <- local (declare (Used av) (ActVar IsNotSubject (ovs :=> desc))) $ sact a
    pure $ FreshMeta r desc (ActorMeta ACitizen av, a)

  Let r av desc t a -> do
    (desc, av, ovs) <- during FreshMetaElaboration $ do
      syndecls <- gets (Map.keys . syntaxCats)
      desc <- sty desc
      av <- isFresh av
      ovs <- asks objVars
      pure (desc, av, ovs)
    t <- stm (LetBound (getRange t)) desc t
    a <- local (declare (Used av) (ActVar IsNotSubject (ovs :=> desc))) $ sact a
    pure (Let r (ActorMeta ACitizen av) desc t a)

  Under r (Scope v@(Hide x) a) -> do
    x <- during UnderElaboration $ isFresh x
    -- TODO: Have the syntax carry a desc? Fail if the hint is Unknown?
    desc <- fromInfo r =<< getHint x
    a <- local (declareObjVar (x, desc)) $ sact a
    pure $ Under r (Scope v a)

  Match r rsc cls -> do
    (esc, sc) <- during (MatchScrutineeElaboration rsc) $ sscrutinee rsc
    chs <- get
    (clsts, cov) <- traverse (sclause esc) cls `runStateT` [escrutinee esc]
    unless (null cov) $ do
      table <- gets syntaxCats
      dat <- asks headUpData
      let examples = fromList cov >>= missing dat table
      raiseWarning r $ MissingClauses examples
    let (cls, sts) = unzip clsts
    let (chst, avst) = unzip $ catMaybes sts
    during (MatchElaboration rsc) $ do
      consistentCommunication  r chst
      consistentScrutinisation r avst
    pure $ Match r sc cls

  Push r stk (rp, (), t) a -> do
    (stk, stkTy) <- isContextStack stk
    (desc, p) <- isObjVar rp
    compatibleInfos (getRange rp) (Known desc) . Known =<< asSemantics (keyDesc stkTy)
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
   _ -> throwComplaint r InconsistentCommunication

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
    _:_:_ -> raiseWarning r InconsistentScrutinisation
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
            IsSubject{} -> raiseWarning r (PatternSubjectNotScrutinised nm)
            _ -> pure ()
    _ -> pure ()

  st <- get
  unless b $ unless (chs == channelStates st) $
    throwComplaint ra (DoomedBranchCommunicated ra)
  put (st { channelStates = chs })
  pure (a, ((,) <$> channelStates <*> actvarStates) st  <$ guard b )

sclause :: EScrutinee -> (RawP, CActor) ->
           StateT [ASemanticsDesc] Elab ((Pat, AActor), Maybe (ChannelStates, ActvarStates))
sclause esc (rp, a) = do
  ds0 <- asks declarations
  avs <- lift $ gets actvarStates
  ovs <- asks objVars
  (mr, p, ds, hs) <- lift $ during (MatchBranchElaboration rp) $ spat esc (initRestriction ovs) rp
  let pats = takez ds (length ds - length ds0)
  coverageCheckClause rp p
  (a, me) <- lift $ during (MatchBranchElaboration rp) $
               local (setDecls ds . setHints hs) $ sbranch (getRange rp) pats a
  lift $ modify (\ st -> st { actvarStates = avs })
  -- make sure no catchall on subject pattern, except in dead branches
  whenJust (me *> mr) (lift . flip raiseWarning UnderscoreOnSubject)
  pure ((p, a), me)

coverageCheckClause :: RawP -> Pat -> StateT [ASemanticsDesc] Elab ()
coverageCheckClause rp p = do
  leftovers <- get
  table <- lift $ gets syntaxCats
  dat <- lift $ asks headUpData
  leftovers <- lift $ case combine $ map (\ d -> (d, shrinkBy dat table d p)) leftovers of
    Covering -> pure []
    AlreadyCovered -> do
      unless (isCatchall p) $
        -- For now we don't complain about catchalls because they may
        -- catching variables.
        raiseWarning rp (UnreachableClause rp)
      pure leftovers
    PartiallyCovering _ ps -> pure ps
  put leftovers


sprotocol :: CProtocol -> Elab AProtocol
sprotocol p = during (ProtocolElaboration p) $ do
  syndecls <- gets (Map.keys . syntaxCats)
  Protocol <$> traverse (bitraverse (traverse $ ssyntaxdesc syndecls) sty) (getProtocol p)

scontextstack :: CContextStack -> Elab AContextStack
scontextstack (ContextStack key val) = do
  syndecls <- gets (Map.keys . syntaxCats)
  key <- ssyntaxdesc syndecls key
  val <- sty val
  pure (ContextStack key val)
