module Elaboration.Pretty where

import Actor (Channel(..))
import Bwd
import Concrete.Pretty()
import Elaboration
import Pretty
import Syntax
import Unelaboration (unsafeEvalUnelab, unelab, initNaming)

instance Pretty Channel where
  pretty (Channel ch) = ch

instance Pretty Mode where
  pretty Input = "?"
  pretty Output = "!"

instance Pretty Protocol where
  pretty = foldMap $ \ (m, c) -> pretty m ++ c ++ ". "

instance Pretty (Info SyntaxCat) where
  prettyPrec d = \case
    Unknown -> "Unknown"
    Known cat -> parenthesise (d > 0) (unwords ["Known", cat])
    Inconsistent -> "Inconsistent"

instance Pretty t => Pretty (JudgementStack t) where
  pretty stk = unwords [keyCat stk, "->", pretty (valueDesc stk)]

instance Pretty Kind where
  pretty = \case
    ActVar{} -> "an object variable"
    AChannel{} -> "a channel"
    AJudgement{} -> "a judgement"

instance Pretty SyntaxDesc where
  pretty t = pretty $ unsafeEvalUnelab initNaming (unelab t)

instance Pretty Complaint where

  pretty = unlines . (<>> []) . go where

    go :: Complaint -> Bwd String
    go = \case
     -- scope
     OutOfScope x -> singleton $ unwords ["Out of scope variable", pretty x]
     MetaScopeTooBig x sc1 sc2 -> singleton $
         unwords [ "Cannot use", pretty x, "here as it is defined in too big a scope"
                 , parens (unwords [ show sc1, "won't fit in", show sc2 ])]
     VariableShadowing x -> singleton $ unwords [pretty x, "is already defined"]
     EmptyContext -> singleton "Tried to pop an empty context"
     NotTopVariable x y -> singleton $
        unwords [ "Expected", pretty x, "to be the top variable"
                , "but found", pretty y, "instead"]
     -- kinding
     NotAValidTermVariable x k -> singleton $
        unwords ["Invalid term variable", pretty x, "refers to", pretty k]
     NotAValidPatternVariable x k -> singleton $
        unwords ["Invalid pattern variable", pretty x, "refers to", pretty k]
     NotAValidJudgement x mk -> singleton $
        unwords ["Invalid judgement variable", pretty x, "refers to", maybe "a bound variable" pretty mk]
     NotAValidChannel x mk -> singleton $
        unwords ["Invalid channel variable", pretty x, "refers to", maybe "a bound variable" pretty mk]
     NotAValidBoundVar x -> singleton $
       unwords ["Invalid bound variable", pretty x]
     -- protocol
     InvalidSend ch -> singleton $ unwords ["Invalid send on channel", pretty ch]
     InvalidRecv ch -> singleton $ unwords ["Invalid receive on channel", pretty ch]
     NonLinearChannelUse ch -> singleton $ unwords ["Non linear use of channel", pretty ch]
     UnfinishedProtocol ch p -> singleton $
       unwords ["Unfinished protocol", parens (pretty p), "on channel", pretty ch]
     InconsistentCommunication -> singleton $ unwords ["Inconsistent communication"]
     DoomedBranchCommunicated a -> singleton $ unwords ["Doomed branch communicated", show a]
      -- judgement stacks
     PushingOnAStacklessJudgement jd -> singleton $ unwords ["Pushing on a stackless judgement", jd]
     LookupFromAStacklessActor jd -> singleton $ unwords ["Lookup from a stackless judgement", jd]
     -- syntaxes
     NotAValidSyntaxCat x -> singleton $ unwords ["Invalid syntactic category", x]
     AlreadyDeclaredSyntaxCat x -> singleton $ unwords ["The syntactic category", x, "is already defined"]
     SyntaxContainsMeta x -> singleton $
       unwords ["The description of the syntactic category", x, "contains meta variables"]
     InvalidSyntax x -> singleton $ unwords ["Invalid description for the syntactic category", x]
  -- syntaxdesc validation
     InconsistentSyntaxCat -> singleton "Inconsistent syntactic categories"
     InvalidSyntaxDesc d -> singleton $ unwords ["Invalid syntax desc", pretty d]
     IncompatibleSyntaxCats cat cat' -> singleton $
       unwords ["Incompatible syntactic categories", prettyPrec 1 cat, "and", prettyPrec 1 cat']
     ExpectedNilGot at -> singleton $ concat ["Expected [] and got", '\'': at]
     ExpectedEnumGot es e -> singleton $ unwords ["Expected an atom among", collapse es, "and got", e]
     ExpectedTagGot ts t -> singleton $ unwords ["Expected a tag among", collapse ts, "and got", t]
     ExpectedANilGot t -> singleton $ unwords ["Expected the term [] and got", pretty t]
     ExpectedANilPGot p -> singleton $ unwords ["Expected the pattern [] and got", pretty p]
     ExpectedAConsGot t -> singleton $ unwords ["Expected a cons cell and got", pretty t]
     ExpectedAConsPGot p -> singleton $ unwords ["Expected a patternf for a cons cell and got", pretty p]
     SyntaxError d t -> singleton $ unwords ["Term", pretty t, "does not match", pretty d]
     SyntaxPError d p -> singleton $ unwords ["Pattern", pretty p, "does not match", pretty d]
     -- contextual info
     SendTermElaboration ch t c -> go c :< unwords [ "when elaborating", pretty ch ++ "!" ++ pretty t ]
     MatchTermElaboration t c -> go c :< unwords [ "when elaborating the case scrutinee", pretty t]
     MatchElaboration t c -> go c :< unwords [ "when elaborating a match with case scrutinee", pretty t]
     MatchBranchElaboration p c -> go c :< unwords [ "when elaborating a case branch handling the pattern", pretty p]
     ConstrainTermElaboration t c -> go c :< unwords [ "when elaborating a constraint involving", pretty t]
     ConstrainSyntaxCatGuess s t c -> go c :< unwords ["when guessing syntactic categories for", pretty s, pretty t]
     FreshMetaElaboration c -> go c :< "when declaring a fresh metavariable"
     UnderElaboration c -> go c :<  "when binding a local variable"
     RecvMetaElaboration ch c -> go c :< unwords ["when receiving a value on channel", pretty ch]
     PushTermElaboration t c -> go c :< unwords ["when pushing the term", pretty t]
     LookupTermElaboration t c -> go c :< unwords [ "when looking up the term", pretty t]
     LookupHandlersElaboration t c ->
        go c :< unwords ["when elaborating the handlers for the lookup acting on", pretty t]
     DeclJElaboration jd c -> go c :< unwords ["when elaborating the judgement declaration for", pretty jd]
     DefnJElaboration jd c -> go c :< unwords ["when elaborating the judgement definition for", pretty jd]
     DeclaringSyntaxCat cat c -> go c :< unwords ["when elaborating the syntax declaration for", cat]
     SubstitutionElaboration sg c -> go c :< unwords ["when elaborating the substitution", pretty sg]
     PatternVariableElaboration v c -> go c :< unwords ["when elaborating the pattern variable", pretty v]
     TermVariableElaboration v c -> go c :< unwords ["when elaborating the term variable", pretty v]
