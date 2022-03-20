{-# LANGUAGE OverloadedStrings #-}

module Elaboration.Pretty where

import Data.Foldable

import Actor (Channel(..))
import Bwd
import Concrete.Pretty()
import Doc
import Doc.Render.Terminal
import Elaboration
import Pretty
import Syntax
import Unelaboration (unsafeEvalUnelab, unelab, initNaming)

instance Pretty Channel where
  pretty (Channel ch) = pretty ch

instance Pretty Mode where
  pretty Input = "?"
  pretty Output = "!"

instance Pretty t => Pretty (Protocol t) where
  pretty = foldMap $ \ (m, d) -> fold [pretty m, pretty d, ". "]

instance Pretty a => Pretty (Info a) where
  prettyPrec d = \case
    Unknown -> "Unknown"
    Known a -> parenthesise (d > 0) (hsep ["Known", prettyPrec 1 a])
    Inconsistent -> "Inconsistent"

instance Pretty t => Pretty (JudgementStack t) where
  pretty stk = hsep [pretty (keyDesc stk), "->", pretty (valueDesc stk)]

instance Pretty Kind where
  pretty = \case
    ActVar{} -> "an object variable"
    AChannel{} -> "a channel"
    AJudgement{} -> "a judgement"

instance Pretty SyntaxDesc where
  pretty t = pretty $ unsafeEvalUnelab initNaming (unelab t)

instance Pretty ObjVar where
  pretty (x, info) = hsep [ pretty x, colon, pretty info ]

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
     NotTopVariable x y -> singleton $
        hsep [ "Expected", pretty x, "to be the top variable"
                , "but found", pretty y, "instead"]
     -- kinding
     NotAValidTermVariable x k -> singleton $
        hsep ["Invalid term variable", pretty x, "refers to", pretty k]
     NotAValidPatternVariable x k -> singleton $
        hsep ["Invalid pattern variable", pretty x, "refers to", pretty k]
     NotAValidJudgement x mk -> singleton $
        hsep ["Invalid judgement variable", pretty x
             , "refers to", maybe "a bound variable" pretty mk]
     NotAValidChannel x mk -> singleton $
        hsep ["Invalid channel variable", pretty x
             , "refers to", maybe "a bound variable" pretty mk]
     NotAValidBoundVar x -> singleton $
       hsep ["Invalid bound variable", pretty x]
     -- protocol
     InvalidSend ch -> singleton $ hsep ["Invalid send on channel", pretty ch]
     InvalidRecv ch -> singleton $ hsep ["Invalid receive on channel", pretty ch]
     NonLinearChannelUse ch -> singleton $ hsep ["Non linear use of channel", pretty ch]
     UnfinishedProtocol ch p -> singleton $
       hsep ["Unfinished protocol", parens (pretty p), "on channel", pretty ch]
     InconsistentCommunication -> singleton $ hsep ["Inconsistent communication"]
     DoomedBranchCommunicated a -> singleton $ hsep ["Doomed branch communicated", pretty a]
      -- judgement stacks
     PushingOnAStacklessJudgement jd -> singleton $ hsep ["Pushing on a stackless judgement", pretty jd]
     LookupFromAStacklessActor jd -> singleton $ hsep ["Lookup from a stackless judgement", pretty jd]
     -- syntaxes
     NotAValidSyntaxCat x -> singleton $ hsep ["Invalid syntactic category", pretty x]
     AlreadyDeclaredSyntaxCat x -> singleton $ hsep ["The syntactic category", pretty x, "is already defined"]
     SyntaxContainsMeta x -> singleton $
       hsep ["The description of the syntactic category", pretty x, "contains meta variables"]
     InvalidSyntax x -> singleton $ hsep ["Invalid description for the syntactic category", pretty x]
  -- syntaxdesc validation
     InconsistentSyntaxDesc -> singleton "Inconsistent syntactic descriptions"
     InvalidSyntaxDesc d -> singleton $ hsep ["Invalid syntax desc", pretty d]
     IncompatibleSyntaxDescs desc desc' -> singleton $
       hsep ["Incompatible syntax descriptions", prettyPrec 1 desc, "and", prettyPrec 1 desc']
     ExpectedNilGot at -> singleton $ hsep ["Expected [] and got", squote <> pretty at]
     ExpectedEnumGot es e -> singleton $ "Expected" <+> sep
       [ hsep [ "an atom among", collapse (map pretty es)]
       , hsep ["and got", pretty e]]
     ExpectedTagGot ts t -> singleton $ "Expected" <+> sep
       [ hsep ["a tag among", collapse (map pretty ts) ]
       , hsep ["and got", pretty t]]
     ExpectedANilGot t -> singleton $ hsep ["Expected the term [] and got", pretty t]
     ExpectedANilPGot p -> singleton $ hsep ["Expected the pattern [] and got", pretty p]
     ExpectedAConsGot t -> singleton $ hsep ["Expected a cons cell and got", pretty t]
     ExpectedAConsPGot p -> singleton $ hsep ["Expected a patternf for a cons cell and got", pretty p]
     SyntaxError d t -> singleton $ hsep ["Term", pretty t, "does not match", pretty d]
     SyntaxPError d p -> singleton $ hsep ["Pattern", pretty p, "does not match", pretty d]
     -- contextual info
     SendTermElaboration ch t c -> go c :< hsep [ "when elaborating", fold [ pretty ch, "!", pretty t ] ]
     MatchTermElaboration t c -> go c :< hsep [ "when elaborating the case scrutinee", pretty t]
     MatchElaboration t c -> go c :< hsep [ "when elaborating a match with case scrutinee", pretty t]
     MatchBranchElaboration p c -> go c :< hsep [ "when elaborating a case branch handling the pattern", pretty p]
     ConstrainTermElaboration t c -> go c :< hsep [ "when elaborating a constraint involving", pretty t]
     ConstrainSyntaxCatGuess s t c -> go c :< hsep ["when guessing syntactic categories for", pretty s, pretty t]
     FreshMetaElaboration c -> go c :< "when declaring a fresh metavariable"
     UnderElaboration c -> go c :<  "when binding a local variable"
     RecvMetaElaboration ch c -> go c :< hsep ["when receiving a value on channel", pretty ch]
     PushTermElaboration t c -> go c :< hsep ["when pushing the term", pretty t]
     LookupTermElaboration t c -> go c :< hsep [ "when looking up the term", pretty t]
     LookupHandlersElaboration t c ->
        go c :< hsep ["when elaborating the handlers for the lookup acting on", pretty t]
     DeclJElaboration jd c -> go c :< hsep ["when elaborating the judgement declaration for", pretty jd]
     DefnJElaboration jd c -> go c :< hsep ["when elaborating the judgement definition for", pretty jd]
     DeclaringSyntaxCat cat c -> go c :< hsep ["when elaborating the syntax declaration for", pretty cat]
     SubstitutionElaboration sg c -> go c :< hsep ["when elaborating the substitution", pretty sg]
     PatternVariableElaboration v c -> go c :< hsep ["when elaborating the pattern variable", pretty v]
     TermVariableElaboration v c -> go c :< hsep ["when elaborating the term variable", pretty v]
     ProtocolElaboration p c -> go c :< hsep ["when elaborating the protocol", pretty p]
