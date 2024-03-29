{-# LANGUAGE OverloadedStrings, UndecidableInstances #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
module Elaboration.Pretty where

import Data.Foldable

import ANSI hiding (withANSI)
import Actor (ActorMeta'(..), ActorMeta, Channel(..), Stack(..), AProtocol)
import Concrete.Base (Binder (..), PROTOCOL(Protocol))
import Concrete.Pretty()
import Elaboration.Monad
import Location
import Pretty
import Unelaboration.Monad (unsafeEvalUnelab, unelab, Unelab, Unelabed, UnelabEnv, Naming)
import Unelaboration ()
import Data.List.NonEmpty (NonEmpty((:|)))
import Syntax ()
import Thin
import Bwd (Bwd (..))

instance Pretty Range where
  pretty r | r == unknown = ""
  pretty r = pretty $ show r

instance Pretty Channel where
  pretty (Channel ch) = pretty ch

instance Pretty Stack where
  pretty (Stack ch) = pretty ch

instance Pretty ActorMeta where
  pretty (ActorMeta _ m) = pretty m

instance Pretty Kind where
  pretty = \case
    ActVar{} -> "an actor variable" -- TODO: terminology?
    AChannel{} -> "a channel"
    AJudgement{} -> "a judgement"
    AStack{} -> "a context stack"

instance Pretty Resolved where
  pretty = \case
    ADeclaration k -> pretty k
    AnObjVar{} -> "a bound variable"
    AMacro t -> "a macro variable"  -- TODO: terminology?

instance (Unelab a, Pretty (Unelabed a), UnelabEnv a ~ Naming)
         => Pretty (WithVarNames a) where
  pretty (WithVarNames ovs a)
    = let naming = (ovs, ones (length ovs), ovs) in
      pretty $ unsafeEvalUnelab naming (unelab a)

instance Pretty AProtocol where
  pretty (Protocol ps) = foldMap (\ x -> pretty (WithVarNames B0 <$> x) <> ". ") ps

instance Pretty (WithRange Warning) where
  pretty (WithRange r w) = (withANSI [ SetColour Background Yellow ] "Warning:" <+> pretty r) $$ go w where

    go :: Warning -> Doc Annotations
    go = \case
      UnreachableClause pat ->
        hsep ["Unreachable clause", pretty pat]
      MissingClauses pats ->
        let sIsAre = case pats of { _ :| [] -> " is"; _ -> "s are" } in
          asBlock 2 ("Incomplete pattern matching. The following pattern" <> sIsAre <+> "missing:")
          $ map pretty (toList pats)
      -- Subject analysis
      SentSubjectNotASubjectVar raw -> hsep ["Sent subject", pretty raw, "is not a subject variable"]
      RecvSubjectNotScrutinised ch (Unused _) -> hsep ["Ignored received subject on channel", pretty ch]
      RecvSubjectNotScrutinised ch (Used x) -> hsep ["Received subject", pretty x,"on channel", pretty ch, "and did not scrutinise it"]
      PatternSubjectNotScrutinised x -> hsep ["Pattern subject", pretty x, "did not get scrutinised"]
      UnderscoreOnSubject -> hsep ["Subject pattern thrown away using an underscore"]
      InconsistentScrutinisation -> hsep ["Inconsistent scrutinisation of subject in match"]
      -- Missing feature
      IgnoredIrrefutable p -> hsep ["TODO: actually implement irrefutable patterns (", pretty p, ")"]

instance Pretty ContextualInfo where
  pretty = \case
    SendTermElaboration ch t -> hsep ["when elaborating", fold [ pretty ch, "!", pretty t ] ]
    MatchScrutineeElaboration t -> hsep ["when elaborating the case scrutinee", pretty t]
    MatchElaboration t -> hsep ["when elaborating a match with case scrutinee", pretty t]
    MatchBranchElaboration p -> hsep ["when elaborating a case branch handling the pattern", pretty p]
    ConstrainTermElaboration t -> hsep ["when elaborating a constraint involving", pretty t]
    ConstrainSyntaxCatGuess s t -> hsep ["when guessing syntactic categories for", pretty s, pretty t]
    CompareTermElaboration t -> hsep ["when elaborating a comparison involving", pretty t]
    ScrutineeTermElaboration t -> hsep ["when elaborating a term scrutinee", pretty t]
    CompareSyntaxCatGuess s t -> hsep ["when guessing syntactic categories for", pretty s, pretty t]
    FreshMetaElaboration -> "when declaring a fresh metavariable"
    UnderElaboration -> "when binding a local variable"
    RecvMetaElaboration ch -> hsep ["when receiving a value on channel", pretty ch]
    PushTermElaboration t -> hsep ["when pushing the term", pretty t]
    LookupVarElaboration t -> hsep ["when looking up the actor variable", pretty t]
    DeclJElaboration jd -> hsep ["when elaborating the judgement declaration for", pretty jd]
    DefnJElaboration jd -> hsep ["when elaborating the judgement definition for", pretty jd]
    ExecElaboration -> hsep ["when elaborating an exec statement"]
    DeclaringSyntaxCat cat -> hsep ["when elaborating the syntax declaration for", pretty cat]
    SubstitutionElaboration sg -> hsep ["when elaborating the substitution", pretty sg]
    PatternVariableElaboration v -> hsep ["when elaborating the pattern variable", pretty v]
    TermVariableElaboration v -> hsep ["when elaborating the term variable", pretty v]
    ProtocolElaboration p -> hsep ["when elaborating the protocol", pretty p]
    ConnectElaboration ch1 ch2 -> hsep ["when elaborating the connection", pretty ch1, "<->", pretty ch2]
    JudgementFormElaboration v -> hsep ["when elaborating the judgement form", pretty v]

instance Pretty (WithRange Complaint) where
  pretty (WithRange r c) = flush (pretty r) <> case c of
    -- scope
    OutOfScope x -> hsep ["Out of scope variable", pretty x]
    MetaScopeTooBig x sc1 sc2 ->
        hsep [ "Cannot use", pretty x
             , "here as it is defined in too big a scope"
             , parens (hsep [ pretty sc1
                            , "won't fit in"
                            , pretty sc2 ])]
    VariableShadowing x -> hsep [pretty x, "is already defined"]
    EmptyContext -> "Tried to pop an empty context"
    NotTopVariable x y ->
          hsep [ "Expected", pretty x, "to be the top variable"
               , "but found", pretty y, "instead"]
    -- kinding
    NotAValidTermVariable x k -> hsep ["Invalid term variable", pretty x, "refers to", pretty k]
    NotAValidPatternVariable x k -> hsep ["Invalid pattern variable", pretty x, "refers to", pretty k]
    NotAValidJudgement x mk ->
       hsep ["Invalid judgement variable", pretty x
            , "refers to", pretty mk]
    NotAValidStack x mk ->
       hsep ["Invalid context stack variable", pretty x
            , "refers to", pretty mk]
    NotAValidChannel x mk ->
       hsep ["Invalid channel variable", pretty x
            , "refers to", pretty mk]
    NotAValidBoundVar x -> hsep ["Invalid bound variable", pretty x]
    NotAValidSubjectVar x -> hsep ["Invalid subject variable", pretty x]
    NotAValidOperator x -> hsep ["Invalid operator name", pretty x]
      -- operators
    AlreadyDeclaredOperator op -> hsep ["Not a valid operator name", pretty op]
    ArityMismatchInOperator op n ->
      let (k, number) = case compare n 0 of
            LT -> (-n, "extra")
            EQ -> error "the impossible happended in ArityMismatchInOperator"
            GT -> (n, "missing")
      in hsep ["Invalid arity:", pretty (show $ k), number, "operator parameters for", pretty op]
    -- protocol
    InvalidSend ch tm -> hsep ["Invalid send of", pretty tm, "on channel", pretty ch]
    InvalidRecv ch v -> hsep ["Invalid receive of", pretty v, "on channel", pretty ch]
    NonLinearChannelUse ch -> hsep ["Non linear use of channel", pretty ch]
    UnfinishedProtocol ch p ->
      hsep ["Unfinished protocol", parens (pretty p), "on channel", pretty ch]
    InconsistentCommunication -> hsep ["Inconsistent communication"]
    DoomedBranchCommunicated a -> hsep ["Doomed branch communicated", pretty a]
    ProtocolsNotDual ps qs -> hsep ["Protocols", pretty ps, "and", pretty qs, "are not dual"]
    IncompatibleModes m1 m2 -> hsep ["Modes", pretty (WithVarNames B0 <$> m1)
                                    , "and", pretty (WithVarNames B0 <$> m2), "are incompatible"]
    IncompatibleChannelScopes sc1 sc2 ->
      hsep [ "Channels scopes", pretty sc1
           , "and", pretty sc2, "are incompatible"]
    WrongDirection m1 dir m2 -> hsep ["Wrong direction", pretty (show dir)
                                     , "between", pretty (WithVarNames B0 <$> m1)
                                     , "and", pretty (WithVarNames B0 <$> m2)]
    -- syntaxes
    AlreadyDeclaredSyntaxCat x -> hsep ["The syntactic category", pretty x, "is already defined"]

  -- syntaxdesc validation
    InconsistentSyntaxDesc -> "Inconsistent syntactic descriptions"
    InvalidSyntaxDesc d -> hsep ["Invalid syntax desc", pretty (WithVarNames B0 d)]
    IncompatibleSemanticsDescs desc desc' ->
      hsep [ "Incompatible semantics descriptions, expected"
           , prettyPrec 1 desc
           , "but got"
           , prettyPrec 1 desc']
    IncompatibleSyntaxInfos info1 info2 ->
      hsep ["Syntax infos" , pretty (WithVarNames B0 <$> info1)
           , "and", pretty (WithVarNames B0 <$> info2)
           , "are incompatible"]
    GotBarredAtom a as -> hsep
      [ squote <> pretty a, "is one of the barred atoms", collapse (map pretty as) ]
    ExpectedNilGot at -> hsep ["Expected [] and got", squote <> pretty at]
    ExpectedEnumGot es e -> sep
      [ "Expected an atom among"
      , collapse $ map pretty es
      , hsep ["and got", pretty e]]
    ExpectedTagGot ts t -> sep
      [ "Expected a tag among"
      , collapse $ map pretty ts
      , hsep ["and got", pretty t]]
    ExpectedANilGot t -> hsep ["Expected the term [] and got", pretty t]
    ExpectedANilPGot p -> hsep ["Expected the pattern [] and got", pretty p]
    ExpectedAConsGot t -> hsep ["Expected a cons cell and got", pretty t]
    ExpectedAConsPGot p -> hsep ["Expected a pattern for a cons cell and got", pretty p]
    SyntaxError d t -> hsep ["Term", pretty t, "does not check against", pretty d]
    SyntaxPError d p -> hsep ["Pattern", pretty p, "does not check against", pretty d]
    CantMatchOnPi d p -> hsep ["Cannot match pattern", pretty p, "at semantic Pi", pretty d]
    CantMatchOnSemantics p -> hsep ["Cannot match on semantics in case", pretty p]
    DuplicatedTag t -> hsep ["Duplicated tag", pretty t]
    ExpectedAnOperator t -> hsep ["Expected an operator call but got", pretty t]
    ExpectedAnEmptyListGot a ds ->
       hsep ["Expected", pretty a, "to be a constant operator"
            , "but it takes arguments of type:", collapse (pretty . WithVarNames B0 <$> ds)]
    InvalidSemanticsDesc sem -> hsep ["Invalid semantics description", pretty sem]
    SemanticsError sem t -> hsep [pretty t, "does not match the semantics description", pretty sem]
    IncompatibleSemanticsInfos isem isem' ->
      hsep ["Incompatible semantics description infos", prettyPrec 1 isem, "and", prettyPrec 1 isem']
    AsPatternCannotHaveSubjects p -> hsep ["As pattern", pretty p, "duplicates a subject variable"]
    -- desc inference
    -- TODO : add more info
    InferredDescMismatch p desc -> hsep [ "Inferred object description", pretty desc
                                        , "does not match pattern", pretty p ]
    DontKnowHowToInferDesc t -> hsep ["Do not know how to infer description for", pretty  t]
    SchematicVariableNotInstantiated -> "Schematic variable not instantiated"
    NotAValidContextRestriction x y -> "Not a valid context restriction"
    NotAValidDescriptionRestriction x y -> "Not a valid description restriction"
    ExpectedParameterBinding x -> "Expected parameter binding"
    ExpectedASemanticsGot t -> hsep ["Expected a semantics but got", pretty t]
    ExpectedASemanticsPGot p -> hsep ["Expected a semantics pattern but got", pretty p]

instance Pretty a => Pretty (WithStackTrace a) where
  pretty (WithStackTrace stk msg) = vcat (pretty msg : map pretty stk)
