module Syntax where

import Control.Monad

import Data.Void
import Data.Map (Map)
import qualified Data.Map as Map

import Bwd
import Thin
import Term

import Display
import Term.Display

type SyntaxCat = String
type SyntaxDesc = CdB (Tm Void)

type SyntaxTable = Map SyntaxCat SyntaxDesc

data VSyntaxDesc
  = VAtom
  | VNil
  | VCons SyntaxDesc SyntaxDesc
  | VNilsOrCons SyntaxDesc SyntaxDesc
  | VBind SyntaxCat SyntaxDesc
  | VTag [(String, [SyntaxDesc])]
  | VEnum [String]
  | VTerm

expand :: SyntaxTable -> SyntaxDesc -> Maybe VSyntaxDesc
expand table = go True where

  go b s = ($ s) $ asTagged $ (. fst) $ \case
    "Rec" -> asTagged $ \ (a,_) _ -> do
      guard b
      s <- Map.lookup a table
      go False s
    "Atom" -> \ _ -> pure VAtom
    "Nil"  -> \ _ -> pure VNil
    "Cons" -> asPair $ \ s0 -> asPair $ \ s1 _ -> pure (VCons s0 s1)
    "NilOrCons" -> asPair $ \ s0 -> asPair $ \ s1 _ -> pure (VNilsOrCons s0 s1)
    "Bind" -> asTagged $ \ (a,_) -> asPair $ \ s _ -> pure (VBind a s)

    "Tag" -> asPair $ asListOf (asTagged $ \ (a, _) ->
                                  asList $ \ bs -> Just (a, bs))
                    $ \ xs _ -> pure (VTag xs)
    "Fix" -> asPair $ asBind $ \ x s' _ -> go False (s' //^ topSbst x s)
    "Enum" -> asPair $ asListOf (asAtom $ Just . fst)
                     $ \ xs _ -> pure (VEnum xs)
    "Term" -> \ _ -> pure VTerm
    _ -> bust

validate :: SyntaxTable -> Bwd SyntaxCat -> SyntaxDesc -> CdB (Tm m) -> Bool
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
   ourLookup  :: String -> CdB (Tm m) -> Maybe (CdB (Tm m))
   ourLookup a = asListOf (asTagged $ \ (a, _) b -> Just (a, b)) $ lookup a

validates :: SyntaxTable -> Bwd SyntaxCat -> [SyntaxDesc] -> CdB (Tm m) -> Bool
validates table env [] = asNil True
validates table env (s:ss) = asPair $ \ t0 t1 ->
  validate table env s t0 && validates table env ss t1

listOf :: SyntaxDesc -> SyntaxDesc
listOf d = let ga = scope d + 1 in
  "Fix" #%+ ["list" \\ (atom "NilOrCons" ga % (weak d % var (DB 0) ga % nil ga))]

rec :: String -> SyntaxDesc
rec a = "Rec" #%+ [atom a 0]

syntaxDesc :: [SyntaxCat] -> SyntaxDesc
syntaxDesc syns = "Tag" #%+ [
  (atom "Rec" 0 % (scats % nil 0)) %
  (atom "Atom" 0 % nil 0) %
  (atom "Nil" 0 % nil 0) %
  (atom "Cons" 0 % (syntax % syntax % nil 0)) %
  (atom "NilOrCons" 0 % (syntax % syntax % nil 0)) %
  (atom "Bind" 0 % (scats % syntax % nil 0)) %
  (atom "Tag" 0 % (listOf (atom "Cons" 0 % atom0 % (listOf syntax % nil 0)) % nil 0)) %
  (atom "Fix" 0 % ("Bind" #%+ [atom "Syntax" 0, syntax]) % nil 0) %
  (atom "Enum" 0 % listOf atom0 % nil 0) %
  (atom "Term" 0 % nil 0) %
  nil 0]
  where syntax = rec "Syntax"
        atom0 = ("Atom",0) #% []
        scats = "Enum" #%+ [foldr (%) (nil 0) $ map (\ s -> atom s 0) syns]


{- > printIt

['Tag
  [['Rec ['Enum ['Syntax]]]
  ['Atom]
  ['Nil]
  ['Cons ['Rec 'Syntax] ['Rec 'Syntax]]
  ['NilOrCons ['Rec 'Syntax] ['Rec 'Syntax]]
  ['Bind ['Enum ['Syntax]] ['Rec 'Syntax]]
  ['Tag ['Fix (\list.['NilOrCons ['Cons ['Atom] ['Fix (\list.['NilOrCons ['Rec 'Syntax] list])]] list])]]
  ['Fix ['Bind 'Syntax ['Rec 'Syntax]]]
  ['Enum ['Fix (\list.['NilOrCons ['Atom] list])]]
  ['Term]]]
-}

validateDesc :: [SyntaxCat] -> SyntaxDesc -> Bool
validateDesc syns =
    validate (Map.singleton "Syntax" (syntaxDesc syns)) B0
     ("Rec" #%+ [atom "Syntax" 0])

validateIt = validateDesc ["Syntax"] (syntaxDesc ["Syntax"])
printIt = putStrLn $ unlines
  [ show validateIt
  , "==="
  , unsafeEvalDisplay initNaming $ display (syntaxDesc ["Syntax"])]
