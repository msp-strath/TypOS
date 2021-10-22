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
validate table env s t = ($ s) $ asTagged $ (. fst) $ \case
  "Rec" -> asTagged $ \ (a,_) _ -> t ?: \case
    VX x _ -> a == bwdProj env x
    _   -> case Map.lookup a table of
      Nothing -> False
      Just s -> validate table env s t
  "Atom" -> \ _ -> ($ t) $ asAtom $ \ (a,_) -> not (null a)
  "Nil"  -> \ _ -> ($ t) $ asAtom $ \ (a,_) -> null a
  "Cons" -> asPair $ \ s0 -> asPair $ \ s1 _ ->
                   ($ t) $ asPair $ \ t0 t1 -> validate table env s0 t0 && validate table env s1 t1
  "Bind" -> asTagged $ \ (a,_) -> asPair $ \ s _ ->
                   ($ t) $ asBind $ \ x t -> validate table (env :< a) s t
  "Tag" -> asPair $ \ s _ ->
                   ($ t) $ asTagged $ \ (a,_) t ->case ourLookup a s of
                                                    Nothing -> False
                                                    Just s  -> validate table env s t
  "Fix" -> asPair $ asBind $ \ x s' _ -> validate table env (s' //^ topSbst x s)  t
  where
   ourLookup  :: String -> Term -> Maybe Term
   ourLookup a = asTagged $ (. fst) $ \case
     "Nil" -> bust
     "Cons" -> asPair $ \ s1 -> asPair $ \ s2 _ -> ($ s1) $ asTagged $ \ (b,_) s ->
       if a == b then Just s else ourLookup a s2

(%:) :: Term -> Term -> Term
s %: t = "Cons" #%+ [s, t]

nul :: Int -> Term
nul ga = ("Nil", ga) #% []

infixr 5 %:

listOf :: SyntaxDesc -> SyntaxDesc
listOf d = let ga = scope d + 1 in
           "Fix" #%+ ["list" \\ ("Tag" #%+ [(atom "Nil" ga % nul ga) %:
                                            (atom "Cons" ga % (weak d %: var 0 ga %: nul ga)) %:
                                            nul ga])]

rec :: String -> SyntaxDesc
rec a = "Rec" #%+ [atom a 0]

syntaxDesc :: SyntaxDesc
syntaxDesc = "Tag" #%+ [
  (atom "Rec" 0 % (atom0 %: nul 0)) %:
  (atom "Atom" 0 % nul 0) %:
  (atom "Nil" 0 % nul 0) %:
  (atom "Cons" 0 % (syntax %: syntax %: nul 0)) %:
  (atom "Bind" 0 % (atom0 %: syntax %: nul 0)) %:
  (atom "Tag" 0 % (listOf (atom0 %: syntax) %: nul 0)) %:
  (atom "Fix" 0 % (("Bind" #%+ [atom "syntax" 0, syntax])) %: nul 0) %:
  nul 0]
  where syntax = rec "syntax"
        atom0 = (("Atom",0) #% [])

-- '[ a b c ] ~~> [ 'Cons a [ 'Cons b [ 'Cons c ['Nil]]]]

-- '[] --> ['Nil]
-- '[a bs] ~~> [ 'Cons a '[bs]]

{- > putStrLn $ display' initNaming syntaxDesc
['Tag
  '[['Rec| '[['Atom]]]
    ['Atom| '[]]
    ['Nil| '[]]
    ['Cons| '[['Rec 'syntax] ['Rec 'syntax]]]
    ['Bind| '[['Atom] ['Rec 'syntax]]]
    ['Tag| '[['Fix \list.['Tag '[['Nil| '[]]
                                 ['Cons| '[['Cons ['Atom] ['Rec 'syntax]] list]]]]]]]
    ['Fix| '[['Bind 'syntax ['Rec 'syntax]]]]]]
-}

-- test = validate syntaxTable B0 ("Rec" #%+ [atom "syntax" 0]) syntaxDesc

