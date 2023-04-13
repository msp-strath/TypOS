{-# LANGUAGE GADTs #-}
module Syntax where

import Control.Monad

import Data.Void
import Data.Map (Map)
import qualified Data.Map as Map

import Bwd
import Concrete.Base (SYNTAXCAT, SYNTAXDESC, Phase(..), ASyntaxDesc)
import Thin (CdB(..), DB(..), weak, scope, lsb)
import Term hiding (contract, expand)
import Location (WithRange)
import Parse (Parser, pwithRange, patom)

type SyntaxCat = String

type instance SYNTAXCAT Concrete = WithRange SyntaxCat
type instance SYNTAXCAT Abstract = SyntaxCat

psyntaxcat :: Parser (SYNTAXCAT Concrete)
psyntaxcat = pwithRange patom

type SyntaxDesc = CdB (Tm Void)
type SyntaxTable = Map SyntaxCat SyntaxDesc

type instance SYNTAXDESC Abstract = SyntaxDesc

data VSyntaxDesc' a
  = VAtom
  | VAtomBar [String]
  | VNil
  | VCons ASyntaxDesc ASyntaxDesc
  | VNilOrCons ASyntaxDesc ASyntaxDesc
  | VBind SyntaxCat ASyntaxDesc
  | VEnumOrTag [String] [(String, [ASyntaxDesc])]
  | VWildcard
  | VSyntaxCat a
  deriving (Eq, Show)

wildcard :: ASyntaxDesc
wildcard = contract VWildcard

type VSyntaxDesc = VSyntaxDesc' Void

data WithSyntaxCat a where
  Yes :: WithSyntaxCat SyntaxCat
  No :: WithSyntaxCat Void

asRec :: OrBust x => (SyntaxCat -> x) -> ASyntaxDesc -> x
asRec f = asAtom $ \ (at, _) -> f at

expand' :: WithSyntaxCat a -> SyntaxTable -> ASyntaxDesc -> Maybe (VSyntaxDesc' a)
expand' w table = go True where

  go b s = ($ s) $ asAtomOrTagged (goAtoms b) (goTagged b s)

  goAtoms b (a,_) = case a of
    "Atom" -> pure VAtom
    "Nil"  -> pure VNil
    "Wildcard" -> pure VWildcard
    a -> do
      s <- Map.lookup a table
      case w of
        Yes -> pure (VSyntaxCat a)
        No -> do guard b
                 go False s

  goTagged b s (a, n) = case a of
    "AtomBar" -> asPair $ asListOf (asAtom $ Just . fst)
                        $ \ xs _ -> pure (VAtomBar xs)
    "Cons" -> asPair $ \ s0 -> asPair $ \ s1 _ -> pure (VCons s0 s1)
    "NilOrCons" -> asPair $ \ s0 -> asPair $ \ s1 _ -> pure (VNilOrCons s0 s1)
    "Bind" -> asTagged $ \ (a,_) -> asPair $ \ s _ -> pure (VBind a s)
    "Tag" -> asPair $ \ s0 s1 -> goTagged b s ("EnumOrTag", n) (nil n % s0 % s1)
    "Enum" -> asPair $ \ s0 s1 -> goTagged b s ("EnumOrTag", n) (s0 % nil n % s1)
    "EnumOrTag" -> asPair $ \ es -> asPair $ \ ts _ ->
                     ($ es) $ asListOf (asAtom $ Just . fst) $ \ xs ->
                     ($ ts) $ asListOf (asTagged $ \ (a, _) -> asList $ \ bs -> Just (a, bs)) $ \ ys ->
                     pure (VEnumOrTag xs ys)
    "Fix" -> asPair $ asBind $ \ x s' _ -> go False (s' //^ topSbst x s)
    _ -> bust

expand :: SyntaxTable -> ASyntaxDesc -> Maybe VSyntaxDesc
expand = expand' No

contract' :: WithSyntaxCat a -> VSyntaxDesc' a -> ASyntaxDesc
contract' w = \case
  VAtom -> atom "Atom" 0
  VAtomBar xs -> "AtomBar" #%+ [enums (\ s -> atom s 0) xs]
  VNil -> atom "Nil" 0
  VCons s t -> "Cons" #%+ [s, t]
  VNilOrCons s t -> "NilOrCons" #%+ [s, t]
  VBind cat s -> "Bind" #%+ [catToDesc cat, s]
  VEnumOrTag es ts -> "EnumOrTag" #%+
    [enums (\ s -> atom s 0) es, enums ( \ (t, s) -> (t,0) #% s) ts]
  VWildcard -> atom "Wildcard" 0
  VSyntaxCat cat -> case w of
    Yes -> atom cat 0
    No -> absurd cat
  where
    enums f = foldr (%) (nil 0) . map f

contract :: VSyntaxDesc -> ASyntaxDesc
contract = contract' No

catToDesc :: SyntaxCat -> ASyntaxDesc
catToDesc c = atom c 0

validate :: Show m => SyntaxTable -> Bwd SyntaxCat -> ASyntaxDesc -> CdB (Tm m) -> Bool
validate table = go where

  go :: Show m => Bwd SyntaxCat -> ASyntaxDesc -> CdB (Tm m) -> Bool
  go env s t@(CdB V th) = reportError s t $ ($ s) $ asRec $ \ a -> a == env <! (dbIndex $ lsb th)
  go env s t = reportError s t $ ($ t) $ flip (maybe bust) (Syntax.expand table s) $ \case
    VAtom -> asAtom $ \ (a,_) -> not (null a)
    VAtomBar as -> asAtom $ \ (a,_) -> not (a `elem` as)
    VNil  -> asAtom $ \ (a,_) -> null a
    VCons s0 s1 -> asPair $ \ t0 t1 -> go env s0 t0 && go env s1 t1
    VNilOrCons s0 s1 -> asNilOrCons True $ \ t0 t1 -> go env s0 t0 && go env s1 t1
    VBind a s -> asBind $ \ x t -> go (env :< a) s t
    VEnumOrTag es ds -> asAtomOrTagged (\ (e,_) -> e `elem` es)
                                       (\ (a,_) t -> case lookup a ds of
                                           Nothing -> False
                                           Just ss -> gos env ss t)
    VWildcard -> \ _ -> True

  reportError :: Show m => ASyntaxDesc -> CdB (Tm m) -> Bool -> Bool
  reportError d t True = True
  reportError d t False = False -- error $ "Validation error\nDesc: " ++ show d ++ "\nTerm: " ++ show t

  gos :: Show m => Bwd SyntaxCat -> [ASyntaxDesc] -> CdB (Tm m) -> Bool
  gos env [] = asNil True
  gos env (s:ss) = asPair $ \ t0 t1 -> go env s t0 && gos env ss t1

listOf :: String -> ASyntaxDesc -> ASyntaxDesc
listOf x d = let ga = scope d + 1 in
  "Fix" #%+ [x \\ (atom "NilOrCons" ga % (weak d % var (DB 0) ga % nil ga))]

rec :: String -> ASyntaxDesc
rec a = atom a 0

syntaxDesc :: [SyntaxCat] -> ASyntaxDesc
syntaxDesc syns = "EnumOrTag" #%+ [
  enums (atoms ++ syns),
  (atom "AtomBar" 0 % (listOf "at" atom0 % nil 0)) %
  (atom "Cons" 0 % (syntax % syntax % nil 0)) %
  (atom "NilOrCons" 0 % (syntax % syntax % nil 0)) %
  (atom "Bind" 0 % (("EnumOrTag" #%+ [enums syns, nil 0]) % syntax % nil 0)) %
  (atom "EnumOrTag" 0 % (listOf "at" atom0
                       % listOf "cell" (atom "Cons" 0 % atom0 % (listOf "rec" syntax % nil 0)) % nil 0)) %
  (atom "Enum" 0 % listOf "at" atom0 % nil 0) %
  (atom "Tag" 0 % (listOf "cell" (atom "Cons" 0 % atom0 % (listOf "rec" syntax % nil 0)) % nil 0)) %
  (atom "Fix" 0 % ("Bind" #%+ [atom "Syntax" 0, syntax]) % nil 0) %
  nil 0]
  where syntax = rec "Syntax"
        atom0 = atom "Atom" 0 -- ("Atom",0) #% []
        atoms = ["Nil", "Atom", "Wildcard"]
        enums sc = foldr (%) (nil 0) $ map (\ s -> atom s 0) sc


{- > printIt

['EnumOrTag
  ['Nil 'Atom 'Wildcard 'Syntax]
  [['AtomBar ['Fix (\list.['NilOrCons 'Atom list])]]
   ['Cons 'Syntax 'Syntax]
   ['NilOrCons 'Syntax 'Syntax]
   ['Bind ['EnumOrTag ['Syntax] []] 'Syntax]
   ['EnumOrTag ['Fix (\list.['NilOrCons 'Atom list])]
               ['Fix (\list.['NilOrCons ['Cons 'Atom ['Fix (\list.['NilOrCons 'Syntax list])]] list])]]
   ['Enum ['Fix (\list.['NilOrCons 'Atom list])]]
   ['Tag ['Fix (\list.['NilOrCons ['Cons 'Atom ['Fix (\list.['NilOrCons 'Syntax list])]] list])]]
   ['Fix ['Bind 'Syntax 'Syntax]]]]

-}

validateDesc :: [SyntaxCat] -> ASyntaxDesc -> Bool
validateDesc syns =
    validate (Map.fromList known) B0
     (rec "Syntax")
  where
     known = [ ("Syntax", syntaxDesc syns)
             , ("Semantics", wildcard)] -- TODO : change


validateIt = validateDesc ["Syntax"] (syntaxDesc ["Syntax"])
