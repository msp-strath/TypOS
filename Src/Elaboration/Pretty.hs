{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
module Elaboration.Pretty where

import Data.Foldable

import Actor (ActorMeta(..), Channel(..))
import Bwd
import Concrete.Base (Mode)
import Concrete.Pretty()
import Doc
import Doc.Render.Terminal
import Elaboration
import Location
import Pretty
import Syntax
import Unelaboration (unsafeEvalUnelab, unelab, initNaming)

instance Pretty Range where
  pretty r | r == unknown = ""
  pretty r = flush (pretty $ show r)

instance Pretty Channel where
  pretty (Channel ch) = pretty ch

instance Pretty ActorMeta where
  pretty (ActorMeta m) = pretty m

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

instance Pretty SyntaxDesc where
  pretty t = pretty $ unsafeEvalUnelab initNaming (unelab t)

instance Pretty ObjVar where
  pretty (x, info) = hsep [ pretty x, colon, pretty info ]

instance Pretty (Mode, SyntaxDesc) where
  pretty (m, desc) = hsep [ pretty m, prettyPrec 1 desc ]

instance Pretty Complaint where

  pretty = vcat . (<>> []) . go where

    go :: Complaint -> Bwd (Doc Annotations)
    go = \case
     -- scope
     OutOfScope x -> singleton $ hsep ["Out of scope variable", pretty x]
     MetaScopeTooBig x sc1 sc2 -> singleton $
         hsep [ "Cannot use", pretty x
              , "here as it is defined in too big a scope"
              , parens (hsep [ collapse (pretty <$> sc1)
                             , "won't fit in"
                             , collapse (pretty <$> sc2) ])]
     VariableShadowing x -> singleton $ hsep [pretty x, "is already defined"]
     EmptyContext -> singleton "Tried to pop an empty context"
     NotTopVariable r x y -> singleton $ pretty r <>
           hsep [ "Expected", pretty x, "to be the top variable"
                , "but found", pretty y, "instead"]
     -- kinding
     NotAValidTermVariable x k -> singleton $
        hsep ["Invalid term variable", pretty x, "refers to", pretty k]
     NotAValidPatternVariable r x k -> singleton $
        pretty r <> hsep ["Invalid pattern variable", pretty x, "refers to", pretty k]
     NotAValidJudgement x mk -> singleton $
        hsep ["Invalid judgement variable", pretty x
             , "refers to", maybe "a bound variable" pretty mk]
     NotAValidChannel x mk -> singleton $
        hsep ["Invalid channel variable", pretty x
             , "refers to", maybe "a bound variable" pretty mk]
     NotAValidBoundVar x -> singleton $
       hsep ["Invalid bound variable", pretty x]
     -- protocol
     InvalidSend ch tm -> singleton $ hsep ["Invalid send of", pretty tm, "on channel", pretty ch]
     InvalidRecv ch v -> singleton $ hsep ["Invalid receive of", pretty v, "on channel", pretty ch]
     NonLinearChannelUse ch -> singleton $ hsep ["Non linear use of channel", pretty ch]
     UnfinishedProtocol ch p -> singleton $
       hsep ["Unfinished protocol", parens (pretty p), "on channel", pretty ch]
     InconsistentCommunication -> singleton $ hsep ["Inconsistent communication"]
     DoomedBranchCommunicated a -> singleton $ hsep ["Doomed branch communicated", pretty a]
     ProtocolsNotDual ps qs -> singleton $ hsep ["Protocols", pretty ps, "and", pretty qs, "are not dual"]
     IncompatibleModes m1 m2 -> singleton $ hsep ["Modes", pretty m1, "and", pretty m2, "are incompatible"]
     IncompatibleChannelScopes sc1 sc2 -> singleton $ hsep ["Channels scopes", collapse (pretty <$> sc1), "and", collapse (pretty <$> sc2), "are incompatible"]
      -- judgement stacks
     PushingOnAStacklessJudgement jd -> singleton $ hsep ["Pushing on a stackless judgement", pretty jd]
     LookupFromAStacklessActor jd -> singleton $ hsep ["Lookup from a stackless judgement", pretty jd]
     -- syntaxes
     NotAValidSyntaxCat x -> singleton $ hsep ["Invalid syntactic category", pretty x]
     AlreadyDeclaredSyntaxCat x -> singleton $ hsep ["The syntactic category", pretty x, "is already defined"]
     SyntaxContainsMeta x -> singleton $
       hsep ["The description of the syntactic category", pretty x, "contains meta variables"]
     InvalidSyntax x -> singleton $ hsep ["Invalid description for the syntactic category", pretty x]
     WrongDirection m1 dir m2 -> singleton $ hsep ["Wrong direction", pretty (show dir), "between", pretty m1, "and", pretty m2]
  -- syntaxdesc validation
     InconsistentSyntaxDesc -> singleton "Inconsistent syntactic descriptions"
     InvalidSyntaxDesc d -> singleton $ hsep ["Invalid syntax desc", pretty d]
     IncompatibleSyntaxDescs desc desc' -> singleton $
       hsep ["Incompatible syntax descriptions", prettyPrec 1 desc, "and", prettyPrec 1 desc']
     IncompatibleSyntaxInfos info1 info2 -> singleton $ hsep ["Syntax infos", pretty info1, "and", pretty info2, "are incompatible"]
     ExpectedNilGot r at -> singleton $ pretty r <> hsep ["Expected [] and got", squote <> pretty at]
     ExpectedEnumGot r es e -> singleton $ pretty r <+> "Expected" <+> sep
       [ hsep ["an atom among", collapse (map pretty es)]
       , hsep ["and got", pretty e]]
     ExpectedTagGot r ts t -> singleton $ pretty r <+> "Expected" <+> sep
       [ hsep ["a tag among", collapse (map pretty ts) ]
       , hsep ["and got", pretty t]]
     ExpectedANilGot r t -> singleton $ pretty r <> hsep ["Expected the term [] and got", pretty t]
     ExpectedANilPGot r p -> singleton $ pretty r <> hsep ["Expected the pattern [] and got", pretty p]
     ExpectedAConsGot r t -> singleton $ pretty r <> hsep ["Expected a cons cell and got", pretty t]
     ExpectedAConsPGot r p -> singleton $ pretty r <> hsep ["Expected a patternf for a cons cell and got", pretty p]
     SyntaxError r d t -> singleton $ pretty r <> hsep ["Term", pretty t, "does not match", pretty d]
     SyntaxPError r d p -> singleton $ pretty r <> hsep ["Pattern", pretty p, "does not match", pretty d]
     -- contextual info
     SendTermElaboration ch t c -> go c :< hsep ["when elaborating", fold [ pretty ch, "!", pretty t ] ]
     MatchTermElaboration t c -> go c :< hsep ["when elaborating the case scrutinee", pretty t]
     MatchElaboration t c -> go c :< hsep ["when elaborating a match with case scrutinee", pretty t]
     MatchBranchElaboration p c -> go c :< hsep ["when elaborating a case branch handling the pattern", pretty p]
     ConstrainTermElaboration t c -> go c :< hsep ["when elaborating a constraint involving", pretty t]
     ConstrainSyntaxCatGuess s t c -> go c :< hsep ["when guessing syntactic categories for", pretty s, pretty t]
     FreshMetaElaboration c -> go c :< "when declaring a fresh metavariable"
     UnderElaboration c -> go c :<  "when binding a local variable"
     RecvMetaElaboration ch c -> go c :< hsep ["when receiving a value on channel", pretty ch]
     PushTermElaboration t c -> go c :< hsep ["when pushing the term", pretty t]
     LookupTermElaboration t c -> go c :< hsep ["when looking up the term", pretty t]
     LookupHandlersElaboration t c ->
        go c :< hsep ["when elaborating the handlers for the lookup acting on", pretty t]
     DeclJElaboration jd c -> go c :< hsep ["when elaborating the judgement declaration for", pretty jd]
     DefnJElaboration jd c -> go c :< hsep ["when elaborating the judgement definition for", pretty jd]
     ExecElaboration c -> go c :< hsep ["when elaborating an exec statement"]
     DeclaringSyntaxCat cat c -> go c :< hsep ["when elaborating the syntax declaration for", pretty cat]
     SubstitutionElaboration sg c -> go c :< hsep ["when elaborating the substitution", pretty sg]
     PatternVariableElaboration v c -> go c :< hsep ["when elaborating the pattern variable", pretty v]
     TermVariableElaboration v c -> go c :< hsep ["when elaborating the term variable", pretty v]
     ProtocolElaboration p c -> go c :< hsep ["when elaborating the protocol", pretty p]
     ConnectElaboration ch1 ch2 c -> go c :< hsep ["when elaborating the connection", pretty ch1, "<->", pretty ch2]
