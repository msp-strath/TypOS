module Elaboration.Pretty where

import Actor (Channel(..))
import Bwd
import Concrete.Pretty()
import Elaboration
import Pretty

instance Pretty Channel where
  pretty (Channel ch) = ch

instance Pretty Mode where
  pretty Input = "?"
  pretty Output = "!"

instance Pretty Protocol where
  pretty = foldMap $ \ (m, c) -> pretty m ++ c ++ ". "

instance Pretty Kind where
  pretty = \case
    ActVar{} -> "an object variable"
    AChannel{} -> "a channel"
    AJudgement{} -> "a judgement"

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
     -- syntaxes
     NotAValidSyntaxCat x -> singleton $ unwords ["Invalid syntactic category", x]
     AlreadyDeclaredSyntaxCat x -> singleton $ unwords ["The syntactic category", x, "is already defined"]
     SyntaxContainsMeta x -> singleton $
       unwords ["The description of the syntactic category", x, "contains meta variables"]
     InvalidSyntax x -> singleton $ unwords ["Invalid description for the syntactic category", x]
     -- contextual info
     SendTermElaboration ch t c -> go c :< unwords [ "when elaborating", pretty ch ++ "!" ++ pretty t ]
     MatchTermElaboration t c -> go c :< unwords [ "when elaborating the case scrutinee", pretty t]
     MatchElaboration t c -> go c :< unwords [ "when elaborating a match with case scrutinee", pretty t]
     MatchBranchElaboration p c -> go c :< unwords [ "when elaborating a case branch handling the pattern", pretty p]
     ConstrainTermElaboration t c -> go c :< unwords [ "when elaborating a constraint involving", pretty t]
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
