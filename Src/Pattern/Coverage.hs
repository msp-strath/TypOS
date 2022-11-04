-- Coverage checker for the pattern language
--
-- The core of the algorithm is based on the `shrinkBy` function.
-- Intuitively, from:
--   1. a SyntaxDesc of the possible inputs
--   2. and a given pattern
-- we attempt to compute:
--   1. the SyntaxDesc the pattern covers
--   2. the SyntaxDesc of the inputs left to cover
module Pattern.Coverage where

import Control.Monad.State (State, evalState, get, put)

import Data.Functor ((<&>))
import Data.List (partition)
import Data.List.NonEmpty (NonEmpty ((:|)), fromList, toList)
import Data.Maybe (fromJust, mapMaybe)

import Concrete.Base (RawP(..), Binder (..), Variable (..), ASyntaxDesc)
import Location (unknown)
import Pattern (Pat'(..))
import Scope (Scope(..))
import Syntax ( VSyntaxDesc'(..), WithSyntaxCat(..), SyntaxTable, VSyntaxDesc, SyntaxCat
              , expand', contract, expand)
import Thin (is1s)
import Hide (Hide(Hide))

------------------------------------------------------------------------------
-- RESULTS
------------------------------------------------------------------------------

-- Possible results of trying to take `pat` away from `desc`.
--
-- /!\ Note that `desc` is not necessarily a well-formed description because
-- it is the result of iteratively subtracting patterns from a valid pattern
-- and some of these patterns may have been overlapping.
-- For instance we cannot assume that in a ['Tag ...] each tag is associated
-- to a single list of syntax descriptions for its payloads.

data Covering' sd
  -- It could be that `pat` has already been covered in a prior pattern.
  -- In which case we will not find a way to subtract it from `desc` e.g.
  -- Pattern:      ['Lam \x.b]
  -- Description:  ['EnumOrTag ['Zero 'Suc] [['Rad 'Synth 'Type]]]
  = AlreadyCovered
  -- It could be that `pat` is general enough that it covers the whole of
  -- `desc`, leaving no leftovers at all e.g. underscores, variables, or:
  -- Pattern:     ['Node _ ['Succ n] ['Leaf a]]
  -- Description: ['Tag [['Node ['Tag [['Leaf 'Nat] ['Node 'Tree ['Enum ['Zero]] 'Tree]]]
  --                            ['Tag [['Succ ['Enum ['Zero]]]]]
  --                            ['Tag [['Leaf 'Nat]]]]]]
  -- We have a full covering because:
  --  1. _         covers ['Tag [['Leaf 'Nat] ['Node 'Tree ['Enum ['Zero]] 'Tree]]]
  --  2. ['Succ n] covers ['Tag [['Succ ['Enum ['Zero]]]]]
  --  3. ['Leaf a] covers ['Tag [['Leaf 'Nat]]]]]]
  | Covering
  -- Finally, in general we only cover part of the input description and return
  -- a list of what is covered and a list of leftovers.
  -- Pattern:      ['Node _ 'Zero _]
  -- Description:  ['Tag [['Node 'Tree 'Nat ['Enum ['Leaf 'Nat]]]
  --                      ['Node ['Enum ['Leaf 'Nat]] 'Nat 'Tree]]]
  ----------------------------------------------------------------------
  -- Covered:  ['Tag [['Node 'Tree                ['Enum ['Zero]]       ['Enum ['Leaf 'Nat]]]
  --                  ['Node ['Enum ['Leaf 'Nat]] ['Enum ['Zero]]       'Tree]]]
  -- Leftover: ['Tag [['Node 'Tree                ['Tag [['Succ 'Nat]]] ['Enum ['Leaf 'Nat]]]
  --                  ['Node ['Enum ['Leaf 'Nat]] ['Tag [['Succ 'Nat]]] 'Tree]]]
  | PartiallyCovering
      [sd] -- what is covered
      [sd] -- what is left to cover
  deriving (Functor)

type Covering = Covering' ASyntaxDesc

------------------------------------------------------------------------------
-- Views

isCovering :: Covering' sd -> Bool
isCovering Covering = True
isCovering _ = False

isAlreadyCovered :: Covering' sd -> Bool
isAlreadyCovered AlreadyCovered = True
isAlreadyCovered _ = False

isPartiallyCovering :: Covering' sd -> Maybe ([sd], [sd])
isPartiallyCovering (PartiallyCovering p ps) = Just (p, ps)
isPartiallyCovering _ = Nothing

------------------------------------------------------------------------------
-- ALGORITHM

-- In general we deal with a list of descriptions of the patterns yet to cover
-- and so our analysis returns a list of `Covering`s for these. We can then call
-- `combine` to compute the final result.
combine :: [(sd, Covering' sd)] -> Covering' sd
combine covs = case partition (isAlreadyCovered . snd) covs of
  -- If all of the pattern is declared to be already covered by *all* of the
  -- alternatives then it has indeed already been covered.
  (_, []) -> AlreadyCovered
  (acs, covs) -> case (acs, partition (isCovering . snd) covs) of
    -- If none of the alternatives claim the pattern has already been covered
    -- and they are all fully covered by the pattern then the pattern is indeed
    -- fully covering.
    ([] , (cds, []))   -> Covering
    -- If some of the alternatives claim the pattern is already covered and the
    -- others claim it is covering, then it is only partially covering and the
    -- leftovers are exactly the descriptions claiming the pattern is already
    -- covered e.g.
    -- Pattern:      ['Succ n]
    -- Descriptions:
    --   ['Enum ['Zero]]                          ----> AlreadyCovered
    --   ['Tag [['Succ ['Tag [['Succ 'Nat]]]]]]   ----> Covering
    --   ['Tag [['Succ ['Enum ['Zero]]]]]         ----> Covering
    ----------------------------------------------------------------------
    -- Result:
    --   PartiallyCovering
    --     [ ['Tag [['Succ ['Tag [['Succ 'Nat]]]]]]
    --     , ['Tag [['Succ ['Enum ['Zero]]]]]
    --     ]
    --     [['Enum ['Zero]]]
    (acs, (cds, []))   -> PartiallyCovering (map fst cds) (map fst acs)
    -- Finally if we have a bit of everything, we have a PartiallyCovering where
    -- for each `(desc, cov)`, if `cov` is:
    --   AlreadyCovered           -> `desc` flows to the leftovers
    --   Covering                 -> `desc` flows to the covered
    --   PartiallyCovering ps qs  -> `ps` flows to the covered
    --                               `qs` flows to the leftovers
    (acs, (cds, covs)) ->
     let (ps, pss) = unzip $ mapMaybe (isPartiallyCovering . snd) covs in
     PartiallyCovering (concat (map fst cds : ps)) $
       concat (map fst acs : pss)

-- Precondition:
--   The pattern has been elaborated against a syntax description that
--   contains the description of the leftovers we are now faced with.
--   So it should not be possible for the description to be incompatible
--   (e.g. 'Atom vs. (PP p q)). It can at most be that the leftovers do
--   not have enough cases to handle the pattern.
-- Postcondition:
--   If `shrinkBy table desc pat` is `PartiallyCovering ps qs` then
--   `desc` is morally equivalent to the sum (ps + qs)
shrinkBy :: forall s. SyntaxTable -> ASyntaxDesc -> Pat' s -> Covering
shrinkBy table = start where

  start :: ASyntaxDesc -> Pat' s -> Covering
  start desc = go (desc, fromJust (expand table desc))

  starts :: [ASyntaxDesc] -> Pat' s -> Covering' [ASyntaxDesc]
  starts descs = gos (map (\ d -> (d, fromJust (expand table d))) descs)

  gos :: [(ASyntaxDesc, VSyntaxDesc)] -> Pat' s -> Covering' [ASyntaxDesc]
  gos [] (AP "") = Covering
  gos (d:ds) (PP p ps) = case (go d p, gos ds ps) of
    (Covering, Covering) -> Covering
    (AlreadyCovered, _) -> AlreadyCovered
    (_, AlreadyCovered) -> AlreadyCovered
    (PartiallyCovering p1 p1s, PartiallyCovering p2 p2s) ->
      PartiallyCovering ((:) <$> p1 <*> p2) $ concat
        [ (:) <$> p1  <*> p2s
        , (:) <$> p1s <*> p2
        , (:) <$> p1s <*> p2s ]
    (PartiallyCovering p1 p1s, Covering) ->
      PartiallyCovering (map (: map fst ds) p1) (map (: map fst ds) p1s)
    (Covering, PartiallyCovering p2 p2s) ->
      PartiallyCovering (map (fst d :) p2) (map (fst d :) p2s)
  gos _ _ = error "Impossible"

  go :: (ASyntaxDesc, VSyntaxDesc) -> Pat' s -> Covering
  go desc (AT s pat) = go desc pat
  go (desc, _) (VP db) = PartiallyCovering [] [desc] -- TODO: handle bound variables too
  go (desc, vdesc) (AP s) = contract <$> case vdesc of
    VAtom -> PartiallyCovering [VEnumOrTag [s] []] [VAtomBar [s]]
    VAtomBar ss | s `notElem` ss ->
      PartiallyCovering [VEnumOrTag [s] []] [VAtomBar (s:ss)]
    VNil | null s -> Covering
    VNilOrCons cb cb' | null s -> PartiallyCovering [VNil] [VCons cb cb']
    VEnumOrTag ss ts ->
      let (matches, ss') = partition (s ==) ss in
      case (ss', ts) of
        _ | null matches -> AlreadyCovered
        ([], []) -> Covering
        _ -> PartiallyCovering [VEnumOrTag matches []] [VEnumOrTag ss' ts]
    VWildcard -> PartiallyCovering [] [VWildcard]
    _ -> AlreadyCovered
  go (desc, vdesc) (PP pat pat') = case vdesc of
    VCons cb cb' -> contract <$> case (start cb pat, start cb' pat') of
      (Covering, Covering) -> Covering
      (AlreadyCovered, _) -> AlreadyCovered
      (_, AlreadyCovered) -> AlreadyCovered
      -- `Cons cb cb'` is the conjunction of `cb` and `cb'`
      -- The recursive results give us:
      -- cb  = p1 + p1s
      -- cb' = p2 + p2s
      -- And the returned result claims that
      -- cb * cb' = p1 * p2 + (p1 * p2s + p1s * p2 + p1s * p2s
      -- which can be easily verified.
      (PartiallyCovering p1 p1s, PartiallyCovering p2 p2s) ->
        PartiallyCovering (VCons <$> p1 <*> p2) $ concat
          [ VCons <$> p1  <*> p2s
          , VCons <$> p1s <*> p2
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
        PartiallyCovering (map (`VCons` cb') p1) (map (`VCons` cb') p1s)
      (Covering, PartiallyCovering p2 p2s) ->
        PartiallyCovering (map (VCons cb) p2) (map (VCons cb) p2s)

    VNilOrCons cb cb' -> contract <$> case (start cb pat, start cb' pat') of
      (Covering, Covering) -> PartiallyCovering [VCons cb cb'] [VNil]
      (AlreadyCovered, _) -> AlreadyCovered
      (_, AlreadyCovered) -> AlreadyCovered
      (PartiallyCovering p1 p1s, PartiallyCovering p2 p2s) ->
        PartiallyCovering (VCons <$> p1 <*> p2) $ concat
          [ [VNil]
          , VCons <$> p1  <*> p2s
          , VCons <$> p1s <*> p2
          , VCons <$> p1s <*> p2s ]
      (PartiallyCovering p1 p1s, Covering) ->
        PartiallyCovering (map (`VCons` cb') p1)
          (VNil : map (`VCons` cb') p1s)
      (Covering, PartiallyCovering p2 p2s) ->
        PartiallyCovering (map (VCons cb) p2)
          (VNil : map (VCons cb) p2s)

    VEnumOrTag ss ts -> case pat of
      AP s ->
        let (matches, ts') = partition ((s ==) . fst) ts in
        contract <$> case combine $ map (\ (_, ds) -> (ds, starts ds pat')) matches of
          _ | null matches -> AlreadyCovered
          Covering | null ss && null ts' -> Covering
          Covering ->
            PartiallyCovering
              [VEnumOrTag [] matches]
              [VEnumOrTag ss ts']
          AlreadyCovered -> AlreadyCovered
          PartiallyCovering p ps ->
            PartiallyCovering
               [VEnumOrTag [] (map (s,) p)]
               [VEnumOrTag ss (map (s,) ps ++ ts')]
      _ -> error "Impossible"
    VWildcard -> contract <$> PartiallyCovering [] [VWildcard]
    _ -> error "Impossible"
  go (desc, vdesc) (BP hi pat) = case vdesc of
    VBind s d -> contract <$> case start d pat of
      Covering -> Covering
      AlreadyCovered -> AlreadyCovered
      PartiallyCovering p ps -> PartiallyCovering (VBind s <$> p) (VBind s <$> ps)
    VWildcard -> contract <$> PartiallyCovering [] [VWildcard]
    _ -> error "Impossible"
  go (desc, vdesc) (MP s th)
    | is1s th = Covering
    | otherwise = PartiallyCovering [] [desc] -- TODO already covered
  go (desc, vdesc) GP = PartiallyCovering [] [desc]
  go _ HP = Covering

missing :: SyntaxTable -> ASyntaxDesc -> NonEmpty RawP
missing table desc = fmap (`evalState` names) (start desc) where

  -- Each solution is a computation using its own name supply because
  -- there is no reason for us not to reuse the same name in independent
  -- patterns e.g. ['Leaf a] and ['Node a b c].
  start :: ASyntaxDesc -> NonEmpty (State [String] RawP)
  start = go . fromJust . expand' Yes table

  -- "a", "b", ..., "z", "a1", "b1", ...
  names :: [String]
  names = concat
        $ zipWith (map . flip (++)) ("" : map show [1..])
        $ repeat (map pure "abcdefghijklmnopqrstuvwxyz")

  freshName :: State [String] String
  freshName = do
    ns <- get
    (n, ns) <- case ns of
      (n:ns) -> pure (n, ns)
      _ -> error "Impossible" -- no type of streams :(
    put ns
    pure n

  go :: VSyntaxDesc' SyntaxCat -> NonEmpty (State [String] RawP)
  go VAtom = (pure $ UnderscoreP unknown) :| []
  go (VAtomBar ss) = (pure $ UnderscoreP unknown) :| []
  go VNil = (pure $ AtP unknown "") :| []
  go (VCons cb cb') = do
    ps <- start cb
    qs <- start cb'
    pure (ConsP unknown <$> ps <*> qs)
  go (VNilOrCons cb cb') = go VNil <> go (VCons cb cb')
  go (VBind s cb) = fmap (LamP unknown . Scope (Hide Unused)) <$> start cb
  go (VEnumOrTag ss ts) =
    let enums = map (\ s -> (pure $ AtP unknown s) :| []) ss
        tagged = ts <&> \ (s, ds) -> do
          args <- traverse start ds
          pure $ ConsP unknown (AtP unknown s) . foldr (ConsP unknown) (AtP unknown "") <$> sequence args
    in fromList (concatMap toList (enums ++ tagged))
  go VWildcard = (pure $ UnderscoreP unknown) :| []
  go (VSyntaxCat _) = (VarP unknown . Variable unknown <$> freshName) :| []
