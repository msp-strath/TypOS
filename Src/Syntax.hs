{-# LANGUAGE GADTs #-}
module Syntax where

import Control.Monad

import Data.Void
import Data.Functor ((<&>))
import Data.Map (Map)
import qualified Data.Map as Map

import Bwd
import Thin (CdB(..), is1s, DB(..), weak, scope, lsb)
import Term hiding (contract, expand)
import Pattern (Pat(..))
import Data.Maybe (fromJust)
import Data.List (partition)
import Hide (Hide(Hide))
import Concrete.Base (RawP(..), Binder (..), Variable (..))
import Location (unknown)
import Scope (Scope(..))
import Control.Monad.State (State, evalState, get, put)
import Data.List.NonEmpty (NonEmpty ((:|)), toList)

appendList :: NonEmpty a -> [a] -> NonEmpty a
appendList xs [] = xs
appendList xs (y : ys) = xs <> (y :| ys)

type SyntaxCat = String
type SyntaxDesc = CdB (Tm Void)

type SyntaxTable = Map SyntaxCat SyntaxDesc

data VSyntaxDesc' a
  = VAtom
  | VAtomBar [String]
  | VNil
  | VCons SyntaxDesc SyntaxDesc
  | VNilOrCons SyntaxDesc SyntaxDesc
  | VBind SyntaxCat SyntaxDesc
  | VEnumOrTag [String] [(String, [SyntaxDesc])]
  | VWildcard
  | VSyntaxCat a
  deriving (Eq, Show)

type VSyntaxDesc = VSyntaxDesc' Void

data WithSyntaxCat a where
  Yes :: WithSyntaxCat SyntaxCat
  No :: WithSyntaxCat Void

asRec :: OrBust x => (SyntaxCat -> x) -> SyntaxDesc -> x
asRec f = asAtom $ \ (at, _) -> f at

expand' :: WithSyntaxCat a -> SyntaxTable -> SyntaxDesc -> Maybe (VSyntaxDesc' a)
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

expand :: SyntaxTable -> SyntaxDesc -> Maybe VSyntaxDesc
expand = expand' No

contract' :: WithSyntaxCat a -> VSyntaxDesc' a -> SyntaxDesc
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

contract :: VSyntaxDesc -> SyntaxDesc
contract = contract' No

catToDesc :: SyntaxCat -> SyntaxDesc
catToDesc c = atom c 0

validate :: Show m => SyntaxTable -> Bwd SyntaxCat -> SyntaxDesc -> CdB (Tm m) -> Bool
validate table = go where

  go :: Show m => Bwd SyntaxCat -> SyntaxDesc -> CdB (Tm m) -> Bool
  go env s t@(CdB V th) = reportError s t $ ($ s) $ asRec $ \ a -> a == bwdProj env (dbIndex $ lsb th)
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

  reportError :: Show m => SyntaxDesc -> CdB (Tm m) -> Bool -> Bool
  reportError d t True = True
  reportError d t False = False -- error $ "Validation error\nDesc: " ++ show d ++ "\nTerm: " ++ show t

  gos :: Show m => Bwd SyntaxCat -> [SyntaxDesc] -> CdB (Tm m) -> Bool
  gos env [] = asNil True
  gos env (s:ss) = asPair $ \ t0 t1 -> go env s t0 && gos env ss t1

listOf :: String -> SyntaxDesc -> SyntaxDesc
listOf x d = let ga = scope d + 1 in
  "Fix" #%+ [x \\ (atom "NilOrCons" ga % (weak d % var (DB 0) ga % nil ga))]

rec :: String -> SyntaxDesc
rec a = atom a 0

syntaxDesc :: [SyntaxCat] -> SyntaxDesc
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

validateDesc :: [SyntaxCat] -> SyntaxDesc -> Bool
validateDesc syns =
    validate (Map.singleton "Syntax" (syntaxDesc syns)) B0
     (rec "Syntax")

validateIt = validateDesc ["Syntax"] (syntaxDesc ["Syntax"])

-- case t : desc
-- { p -> .. desc \ p
-- ; q -> .. desc \ p \ q
-- ; r -> .. desc \ p \ q \ r === []
-- }

data Covering' sd
  = AlreadyCovered
  | Covering
  | PartiallyCovering
      sd   -- what is covered
      [sd] -- what is left to cover
  deriving (Functor)

type Covering = Covering' SyntaxDesc

-- These semigroup & monoid instances try to merge all of the
-- information for a set of disjoint descriptions the pattern
-- could match
instance Semigroup (Covering' sd) where
  AlreadyCovered <> c = c
  c <> AlreadyCovered = c
  Covering <> c = c
  c <> Covering = c
  PartiallyCovering p ps <> PartiallyCovering q qs
    = PartiallyCovering p (ps ++ qs)

instance Monoid (Covering' sd) where
  mempty = AlreadyCovered

-- Precondition:
--   The pattern has been elaborated against a description that contains the
--   description so it should not be possible for the description to be incompatible.
--   It can at most not have enough cases to handle the pat.
-- Postcondition:
--   The output is a description corresponding to the original one minus the case
--   covered by the input pattern.
shrinkBy :: SyntaxTable -> SyntaxDesc -> Pat -> Covering
shrinkBy table = start where

  vempty :: VSyntaxDesc
  vempty = VEnumOrTag [] []

  empty :: SyntaxDesc
  empty = contract $ VEnumOrTag [] []

  start :: SyntaxDesc -> Pat -> Covering
  start desc = go (desc, fromJust (expand table desc))

  starts :: [SyntaxDesc] -> Pat -> Covering' [SyntaxDesc]
  starts descs = gos (map (\ d -> (d, fromJust (expand table d))) descs)

  gos :: [(SyntaxDesc, VSyntaxDesc)] -> Pat -> Covering' [SyntaxDesc]
  gos [] (AP "") = Covering
  gos (d:ds) (PP p ps) = case (go d p, gos ds ps) of
    (Covering, Covering) -> Covering
    (AlreadyCovered, _) -> AlreadyCovered
    (_, AlreadyCovered) -> AlreadyCovered
    (PartiallyCovering p1 p1s, PartiallyCovering p2 p2s) ->
      PartiallyCovering (p1 : p2) $ concat
        [ map (p1 :) p2s
        , map (: p2) p1s
        , (:) <$> p1s <*> p2s ]
    (PartiallyCovering p1 p1s, Covering) ->
      PartiallyCovering (p1 : map fst ds) (map (: map fst ds) p1s)
    (Covering, PartiallyCovering p2 p2s) ->
      PartiallyCovering (fst d : p2) (map (fst d :) p2s)
  gos _ _ = error "Impossible"

  go :: (SyntaxDesc, VSyntaxDesc) -> Pat -> Covering
  go desc (AT s pat) = go desc pat
  go (desc, _) (VP db) = PartiallyCovering empty [desc] -- TODO: handle bound variables too
  go (desc, vdesc) (AP s) = contract <$> case vdesc of
    VAtom -> PartiallyCovering (VEnumOrTag [s] []) [VAtomBar [s]]
    VAtomBar ss | s `notElem` ss -> PartiallyCovering (VEnumOrTag [s] []) [VAtomBar (s:ss)]
    VNil | null s -> Covering
    VNilOrCons cb cb' | null s -> PartiallyCovering VNil [VCons cb cb']
    VEnumOrTag ss ts ->
      let (matches, ss') = partition (s ==) ss in
      case (ss', ts) of
        _ | null matches -> AlreadyCovered
        ([], []) -> Covering
        _ -> PartiallyCovering (VEnumOrTag matches []) [VEnumOrTag ss' ts]
    VWildcard -> PartiallyCovering vempty [VWildcard]
    _ -> AlreadyCovered
  go (desc, vdesc) (PP pat pat') = case vdesc of
    VCons cb cb' -> contract <$> case (start cb pat, start cb' pat') of
      (Covering, Covering) -> Covering
      (AlreadyCovered, _) -> AlreadyCovered
      (_, AlreadyCovered) -> AlreadyCovered
      (PartiallyCovering p1 p1s, PartiallyCovering p2 p2s) ->
        PartiallyCovering (VCons p1 p2) $ concat
          [ map (VCons p1) p2s
          , map (`VCons` p2) p1s
          , VCons <$> p1s <*> p2s ]
-- Input desc: ['Cons ['Enum ['a 'b 'c]] ['Enum ['d 'e 'f]]]
-- Pattern: ['a | 'e]
-- Recursive calls:
-- Left:  PartiallyCovering ['Enum ['a]] [['Enum ['b 'c]]]
-- Right: PartiallyCovering ['Enum ['e]] [['Enum ['d 'f]]]
--------------------------------------------------------------
-- PartiallyCovering
--   ['Cons ['Enum ['a]] ['Enum ['e]]]
--   [ ['Cons ['Enum ['a]]    ['Enum ['d 'f]]]
--     ['Cons ['Enum ['b 'c]] ['Enum ['e]]]
--     ['Cons ['Enum ['b 'c]] ['Enum ['d 'f]]]]
      (PartiallyCovering p1 p1s, Covering) ->
        PartiallyCovering (VCons p1 cb') (map (`VCons` cb') p1s)
      (Covering, PartiallyCovering p2 p2s) ->
        PartiallyCovering (VCons cb p2) (map (VCons cb) p2s)

    VNilOrCons cb cb' -> contract <$> case (start cb pat, start cb' pat') of
      (Covering, Covering) -> PartiallyCovering (VCons cb cb') [VNil]
      (AlreadyCovered, _) -> AlreadyCovered
      (_, AlreadyCovered) -> AlreadyCovered
      (PartiallyCovering p1 p1s, PartiallyCovering p2 p2s) ->
        PartiallyCovering (VCons p1 p2) $ concat
          [ [VNil]
          , map (VCons p1) p2s
          , map (`VCons` p2) p1s
          , VCons <$> p1s <*> p2s ]
      (PartiallyCovering p1 p1s, Covering) ->
        PartiallyCovering (VCons p1 cb') (VNil : map (`VCons` cb') p1s)
      (Covering, PartiallyCovering p2 p2s) ->
        PartiallyCovering (VCons cb p2) (VNil : map (VCons cb) p2s)

    VEnumOrTag ss ts -> case pat of
      AP s ->
        let (matches, ts') = partition ((s ==) . fst) ts in
        contract <$> case foldMap (\ (_, ds) -> starts ds pat') matches of
          Covering | null ss && null ts' -> Covering
          Covering -> PartiallyCovering (VEnumOrTag [] matches) [VEnumOrTag ss ts']
          AlreadyCovered -> AlreadyCovered
          PartiallyCovering p ps ->
            PartiallyCovering
               (VEnumOrTag [] [(s, p)])
               [VEnumOrTag ss (map (s,) ps ++ ts')]
      _ -> error "Impossible"
    VWildcard -> contract <$> PartiallyCovering vempty [VWildcard]
    _ -> error "Impossible"
  go (desc, vdesc) (BP hi pat) = case vdesc of
    VBind s d -> contract <$> case start d pat of
      Covering -> Covering
      AlreadyCovered -> AlreadyCovered
      PartiallyCovering p ps -> PartiallyCovering (VBind s p) (VBind s <$> ps)
    VWildcard -> contract <$> PartiallyCovering vempty [VWildcard]
    _ -> error "Impossible"
  go (desc, vdesc) (MP s th)
    | is1s th = Covering
    | otherwise = PartiallyCovering empty [desc] -- TODO already covered
  go (desc, vdesc) GP = PartiallyCovering empty [desc]
  go _ HP = Covering

missing :: SyntaxTable -> SyntaxDesc -> NonEmpty RawP
missing table desc = fmap (`evalState` names) (start desc) where

  names :: [String]
  names = concat
        $ zipWith (map . flip (++)) ("" : map show [1..])
        $ repeat (map pure "abcdefghijklmnopqrstuvwxyz")

  start :: SyntaxDesc -> NonEmpty (State [String] RawP)
  start = go . fromJust . expand' Yes table

  go :: VSyntaxDesc' SyntaxCat -> NonEmpty (State [String] RawP)
  go VAtom = (pure $ UnderscoreP unknown) :| []
  go (VAtomBar ss) = (pure $ UnderscoreP unknown) :| []
  go VNil = (pure $ AtP unknown "") :| []
  go (VCons cb cb') = do
    ps <- start cb
    qs <- start cb'
    pure (ConsP unknown <$> ps <*> qs)
  go (VNilOrCons cb cb') = (pure $ AtP unknown "") :| []
  go (VBind s cb) = fmap (LamP unknown . Scope (Hide Unused)) <$> start cb
  go (VEnumOrTag ss ts) =
    let enums = map (\ s -> (pure $ AtP unknown s) :| []) ss
        tagged = ts <&> \ (s, ds) -> do
          args <- traverse start ds
          pure $ ConsP unknown (AtP unknown s) . foldr (ConsP unknown) (AtP unknown "") <$> sequence args
    in case enums ++ tagged of
      (p : ps) -> p `appendList` concatMap toList ps
      [] -> error "Impossible"
  go VWildcard = (pure $ UnderscoreP unknown) :| []
  go (VSyntaxCat _) = (:| []) $ do
    ns <- get
    (n, ns) <- case ns of
                 (n:ns) -> pure (n, ns)
                 _ -> error "Impossible"
    put ns
    pure $ VarP unknown $ Variable unknown n
