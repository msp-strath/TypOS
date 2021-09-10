{-# LANGUAGE PatternSynonyms
           , LambdaCase
#-}
module Syntax where

import qualified Data.Map as Map

import Bwd
import Thin
import Term

type SyntaxCat = String
type SyntaxDesc = Term

validate :: Map.Map SyntaxCat SyntaxDesc -> Bwd SyntaxCat -> SyntaxDesc -> Term -> Bool
validate table env s t = s #%< \case
  "Rec" -> flip (#%<) $ \ a _ -> t ?: \case
    VX x _ -> a == bwdProj env x
    _   -> case Map.lookup a table of
      Nothing -> False
      Just s -> validate table env s t
  "Atom" -> \ _ -> t ?: \case
    AX (_:_) -> True
    _        -> False
  "Nil" -> \ _ -> t ?: \case
    AX "" -> True
    _     -> False
  "Cons" -> flip (%<) $ \ s1 -> flip (%<) $ \ s2 _ -> t ?: \case
    t0 :%: t1 -> validate table env s1 t0 && validate table env s2 t1
    _         -> False
  "Bind" -> flip (#%<) $ \ a -> flip (%<) $ \ s _ -> t ?: \case
    x :.: t -> validate table (env :< a) s t
    _       -> False
  "Tag" -> flip (%<) $ \ s _ -> t ?: \case
    ((A a, _) :%: t1) -> case ourLookup a s of
      Nothing -> False
      Just s  -> validate table env s t1
    _                -> False
  "Fix" -> flip (%<) $ \ s' _ -> validate table env (under s' ^// topSbst s) t
  where
   ourLookup  :: String -> Term -> Maybe Term
   ourLookup a s = s #%< \case
     "Nil" -> \ _ -> Nothing
     "Cons" -> flip (%<) $ \ s1 -> flip (%<) $ \ s2 _ -> s1 #%< \ b s ->
       if a == b then Just s else ourLookup a s2

(%:) :: Term -> Term -> Term
s %: t = "Cons" #% [s, t]

nul :: Term
nul = "Nil" #% []

infixr 5 %:

listOf :: SyntaxDesc -> SyntaxDesc
listOf d = "Fix" #% ["list" \\ ("Tag" #% [(atom "Nil" % nul) %:
                                          (atom "Cons" % (weak d %: var 0 %: nul)) %:
                                          nul])]

syntaxTable :: Map.Map SyntaxCat SyntaxDesc
syntaxTable = Map.singleton "syntax" syntaxDesc

syntaxDesc :: SyntaxDesc
syntaxDesc = "Tag" #% [
  (atom "Rec" % (("Atom" #% []) %: nul)) %:
  (atom "Atom" % nul) %:
  (atom "Nil" % nul) %:
  (atom "Cons" % (syntax %: syntax %: nul)) %:
  (atom "Bind" % (("Atom" #% []) %: syntax %: nul)) %:
  (atom "Tag" % (listOf (("Atom" #% []) %: syntax) %: nul)) %:
  (atom "Fix" % (("Bind" #% [atom "syntax" , syntax])) %: nul) %:
  nul]
  where syntax = "Rec" #% [atom "syntax"]

-- test = validate syntaxTable B0 ("Rec" #% [atom "syntax"]) syntaxDesc
