module Syntax where

import qualified Data.Map as Map

import Bwd
import Thin
import Term

type SyntaxCat = String
type SyntaxDesc = Term

type SyntaxTable = Map.Map SyntaxCat SyntaxDesc

validate :: SyntaxTable -> Bwd SyntaxCat -> SyntaxDesc -> Term -> Bool
validate table env s t
  = ($ s) $ asTagged $ (. fst) $ \case
  "Rec" -> asTagged $ \ (a,_) _ -> t ?: \case
    VX x _ -> a == bwdProj env (dbIndex x)
    _   -> case Map.lookup a table of
      Nothing -> False
      Just s -> validate table env s t
  "Atom" -> \ _ -> ($ t) $ asAtom $ \ (a,_) -> not (null a)
  "Nil"  -> \ _ -> ($ t) $ asAtom $ \ (a,_) -> null a
  "Cons" -> asPair $ \ s0 -> asPair $ \ s1 _ ->
                   ($ t) $ asPair $ \ t0 t1 -> validate table env s0 t0 && validate table env s1 t1
  "NilOrCons" -> asPair $ \ s0 -> asPair $ \ s1 _ ->
                   ($ t) $ asNilOrCons True $ \ t0 t1 -> validate table env s0 t0 && validate table env s1 t1
  "Bind" -> asTagged $ \ (a,_) -> asPair $ \ s _ ->
                   ($ t) $ asBind $ \ x t -> validate table (env :< a) s t
  "Tag" -> asPair $ \ s _ ->
                   ($ t) $ asTagged $ \ (a,_) t -> case ourLookup a s of
                         Nothing -> False
                         Just s -> ($ s) $ asList $ \ ss -> validates table env ss t
  "Fix" -> asPair $ asBind $ \ x s' _ -> validate table env (s' //^ topSbst x s)  t
  "Enum" -> asPair $ asListOf (asAtom $ Just . fst) $ \es -> asNil $ ($ t) $ asAtom $ \ (e,_) -> e `elem` es
  "Term" -> \ _ -> True
  where
   ourLookup  :: String -> Term -> Maybe Term
   ourLookup a = asListOf (asTagged $ \ (a, _) b -> Just (a, b)) $ lookup a


validates :: SyntaxTable -> Bwd SyntaxCat -> [SyntaxDesc] -> Term -> Bool
validates table env [] = asNil True
validates table env (s:ss) = asPair $ \ t0 t1 ->
  validate table env s t0 && validates table env ss t1

(%:) :: Term -> Term -> Term
s %: t = s % t

nul :: Int -> Term
nul = nil

infixr 5 %:

listOf :: SyntaxDesc -> SyntaxDesc
listOf d = let ga = scope d + 1 in
  "Fix" #%+ ["list" \\ (atom "NilOrCons" ga % (weak d %: var (DB 0) ga %: nul ga))]

rec :: String -> SyntaxDesc
rec a = "Rec" #%+ [atom a 0]

syntaxDesc :: SyntaxDesc
syntaxDesc = "Tag" #%+ [
  (atom "Rec" 0 % (atom0 %: nul 0)) %:
  (atom "Atom" 0 % nul 0) %:
  (atom "Nil" 0 % nul 0) %:
  (atom "Cons" 0 % (syntax %: syntax %: nul 0)) %:
  (atom "NilOrCons" 0 % (syntax %: syntax %: nul 0)) %:
  (atom "Bind" 0 % (atom0 %: syntax %: nul 0)) %:
  (atom "Tag" 0 % (listOf (atom "Cons" 0 % atom0 %: (listOf syntax %: nul 0)) %: nul 0)) %:
  (atom "Fix" 0 % ("Bind" #%+ [atom "syntax" 0, syntax]) %: nul 0) %:
  (atom "Enum" 0 % listOf atom0 %: nul 0) %:
  (atom "Term" 0 % nul 0) %:
  nul 0]
  where syntax = rec "syntax"
        atom0 = ("Atom",0) #% []

{- > putStrLn $ display initNaming syntaxDesc

['Tag [
  ['Rec ['Atom]]
  ['Atom]
  ['Nil]
  ['Cons ['Rec 'syntax] ['Rec 'syntax]]
  ['NilOrCons ['Rec 'syntax] ['Rec 'syntax]]
  ['Bind ['Atom] ['Rec 'syntax]]
  ['Tag ['Fix (\list.['NilOrCons ['Cons ['Atom] ['Fix (\list.['NilOrCons ['Rec 'syntax] list])]] list])]]
  ['Fix ['Bind 'syntax ['Rec 'syntax]]]
  ['Enum ['Fix (\list.['NilOrCons ['Atom] list])]]
  ['Term]
]]

-}

validateDesc :: SyntaxDesc -> Bool
validateDesc = validate (Map.singleton "syntax" syntaxDesc) B0 ("Rec" #%+ [atom "syntax" 0])

test = validateDesc syntaxDesc
