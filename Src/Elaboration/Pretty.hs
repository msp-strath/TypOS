{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
module Elaboration.Pretty where

import Data.Foldable

import ANSI hiding (withANSI)
import Actor (ActorMeta(..), Channel(..), Stack(..))
import Concrete.Base (Mode, Binder (..))
import Concrete.Pretty()
import Elaboration.Monad
import Location
import Pretty
import Syntax
import Unelaboration (unsafeEvalUnelab, unelab, initNaming)
import Data.List.NonEmpty (NonEmpty((:|)))

instance Pretty Range where
  pretty r | r == unknown = ""
  pretty r = pretty $ show r

instance Pretty Channel where
  pretty (Channel ch) = pretty ch

instance Pretty Stack where
  pretty (Stack ch) = pretty ch

instance Pretty ActorMeta where
  pretty (ActorMeta _ m) = pretty m

instance Pretty a => Pretty (Info a) where
  prettyPrec d = \case
    Unknown -> "Unknown"
    Known a -> parenthesise (d > 0) (hsep ["Known", prettyPrec 1 a])
    Inconsistent -> "Inconsistent"

instance Pretty Kind where
  pretty = \case
    ActVar{} -> "an object variable"
    AChannel{} -> "a channel"
    AJudgement{} -> "a judgement"
    AStack{} -> "a context stack"

instance Pretty SyntaxDesc where
  pretty t = pretty $ unsafeEvalUnelab initNaming (unelab t)

instance Pretty ObjVar where
  pretty (x, info) = hsep [ pretty x, colon, pretty info ]

instance Pretty (Mode, SyntaxDesc) where
  pretty (m, desc) = hsep [ pretty m, prettyPrec 1 desc ]

instance Pretty Warning where
  pretty w = (withANSI [ SetColour Background Yellow ] "Warning:" <+> pretty (getRange w)) $$ go w where

    go :: Warning -> Doc Annotations
    go = \case
      UnreachableClause r pat ->
        hsep ["Unreachable clause", pretty pat]
      MissingClauses r pats ->
        let sIsAre = case pats of { _ :| [] -> " is"; _ -> "s are" } in
          asBlock 2 ("Incomplete pattern matching. The following pattern" <> sIsAre <+> "missing:")
          $ map pretty (toList pats)
      -- Subject analysis
      SentSubjectNotASubjectVar r raw -> hsep ["Sent subject", pretty raw, "is not a subject variable"]
      RecvSubjectNotScrutinised r ch Unused -> hsep ["Ignored received subject on channel", pretty ch]
      RecvSubjectNotScrutinised r ch (Used x) -> hsep ["Received subject", pretty x,"on channel", pretty ch, "and did not scrutinise it"]
      PatternSubjectNotScrutinised r x -> hsep ["Pattern subject", pretty x, "did not get scrutinised"]
      UnderscoreOnSubject r -> hsep ["Subject pattern thrown away using an underscore"]
      InconsistentScrutinisation r -> hsep ["Inconsistent scrutinisation of subject in match"]

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

instance Pretty Complaint where
  pretty c = flush (pretty (getRange c)) <> case c of
    -- scope
    OutOfScope r x -> hsep ["Out of scope variable", pretty x]
    MetaScopeTooBig r x sc1 sc2 ->
        hsep [ "Cannot use", pretty x
             , "here as it is defined in too big a scope"
             , parens (hsep [ collapse (pretty <$> sc1)
                            , "won't fit in"
                            , collapse (pretty <$> sc2) ])]
    VariableShadowing r x -> hsep [pretty x, "is already defined"]
    EmptyContext r -> "Tried to pop an empty context"
    NotTopVariable r x y ->
          hsep [ "Expected", pretty x, "to be the top variable"
               , "but found", pretty y, "instead"]
    -- kinding
    NotAValidTermVariable r x k -> hsep ["Invalid term variable", pretty x, "refers to", pretty k]
    NotAValidPatternVariable r x k -> hsep ["Invalid pattern variable", pretty x, "refers to", pretty k]
    NotAValidJudgement r x mk ->
       hsep ["Invalid judgement variable", pretty x
            , "refers to", maybe "a bound variable" pretty mk]
    NotAValidStack r x mk ->
       hsep ["Invalid context stack variable", pretty x
            , "refers to", maybe "a bound variable" pretty mk]
    NotAValidChannel r x mk ->
       hsep ["Invalid channel variable", pretty x
            , "refers to", maybe "a bound variable" pretty mk]
    NotAValidBoundVar r x -> hsep ["Invalid bound variable", pretty x]
    NotAValidSubjectVar r x -> hsep ["Invalid subject variable", pretty x]
    NotAValidOperator r x -> hsep ["Invalid operator name", pretty x]
      -- operators
    AlreadyDeclaredOperator r op -> hsep ["Not a valid operator name", pretty op]
    InvalidOperatorArity r op [] ops ->
      hsep ["Invalid arity:", pretty (show $ length ops), "extra operator parameters for", pretty op]
    InvalidOperatorArity r op ds [] ->
      hsep ["Invalid arity:", pretty (show $ length ds), "missing operator parameters for", pretty op]
    InvalidOperatorArity r op ds ps ->
      hsep ["Invalid arity (the impossible happened)"]
    -- protocol
    InvalidSend r ch tm -> hsep ["Invalid send of", pretty tm, "on channel", pretty ch]
    InvalidRecv r ch v -> hsep ["Invalid receive of", pretty v, "on channel", pretty ch]
    NonLinearChannelUse r ch -> hsep ["Non linear use of channel", pretty ch]
    UnfinishedProtocol r ch p ->
      hsep ["Unfinished protocol", parens (pretty p), "on channel", pretty ch]
    InconsistentCommunication r -> hsep ["Inconsistent communication"]
    DoomedBranchCommunicated r a -> hsep ["Doomed branch communicated", pretty a]
    ProtocolsNotDual r ps qs -> hsep ["Protocols", pretty ps, "and", pretty qs, "are not dual"]
    IncompatibleModes r m1 m2 -> hsep ["Modes", pretty m1, "and", pretty m2, "are incompatible"]
    IncompatibleChannelScopes r sc1 sc2 ->
      hsep [ "Channels scopes", collapse (pretty <$> sc1)
           , "and", collapse (pretty <$> sc2), "are incompatible"]
    -- syntaxes
    AlreadyDeclaredSyntaxCat r x -> hsep ["The syntactic category", pretty x, "is already defined"]
    WrongDirection r m1 dir m2 -> hsep ["Wrong direction", pretty (show dir), "between", pretty m1, "and", pretty m2]
  -- syntaxdesc validation
    InconsistentSyntaxDesc r -> "Inconsistent syntactic descriptions"
    InvalidSyntaxDesc r d -> hsep ["Invalid syntax desc", pretty d]
    IncompatibleSyntaxDescs r desc desc' ->
      hsep ["Incompatible syntax descriptions", prettyPrec 1 desc, "and", prettyPrec 1 desc']
    IncompatibleSyntaxInfos r info1 info2 ->
      hsep ["Syntax infos", pretty info1, "and", pretty info2, "are incompatible"]
    GotBarredAtom r a as -> hsep
      [ squote <> pretty a, "is one of the barred atoms", collapse (map pretty as) ]
    ExpectedNilGot r at -> hsep ["Expected [] and got", squote <> pretty at]
    ExpectedEnumGot r es e -> sep
      [ "Expected an atom among"
      , collapse $ map pretty es
      , hsep ["and got", pretty e]]
    ExpectedTagGot r ts t -> sep
      [ "Expected a tag among"
      , collapse $ map pretty ts
      , hsep ["and got", pretty t]]
    ExpectedANilGot r t -> hsep ["Expected the term [] and got", pretty t]
    ExpectedANilPGot r p -> hsep ["Expected the pattern [] and got", pretty p]
    ExpectedAConsGot r t -> hsep ["Expected a cons cell and got", pretty t]
    ExpectedAConsPGot r p -> hsep ["Expected a pattern for a cons cell and got", pretty p]
    SyntaxError r d t -> hsep ["Term", pretty t, "does not match", pretty d]
    SyntaxPError r d p -> hsep ["Pattern", pretty p, "does not match", pretty d]
    ExpectedAnOperator r t -> hsep ["Expected an operator call but got", pretty t]
    ExpectedAnEmptyListGot r a ds ->
       hsep ["Expected", pretty a, "to be a constant operator"
            , "but it takes arguments of type:", collapse (pretty <$> ds)]
    AsPatternCannotHaveSubjects r p -> hsep ["As pattern", pretty p, "duplicates a subject variable"]

instance Pretty a => Pretty (WithStackTrace a) where
  pretty (WithStackTrace stk msg) = vcat (pretty msg : map pretty stk)
