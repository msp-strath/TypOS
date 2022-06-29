module Pattern.Coverage where

import Control.Monad.State (State, evalState, get, put)

import Data.Functor ((<&>))
import Data.List (partition)
import Data.List.NonEmpty (NonEmpty ((:|)), fromList, toList)
import Data.Maybe (fromJust, mapMaybe)

import Concrete.Base (RawP(..), Binder (..), Variable (..))
import Location (unknown)
import Pattern (Pat(..))
import Scope (Scope(..))
import Syntax ( SyntaxDesc, VSyntaxDesc'(..), WithSyntaxCat(..), SyntaxTable, VSyntaxDesc, SyntaxCat
              , expand', contract, expand)
import Thin (is1s)
import Hide (Hide(Hide))

data Covering' sd
  = AlreadyCovered
  | Covering
  | PartiallyCovering
      [sd] -- what is covered
      [sd] -- what is left to cover
  deriving (Functor)

type Covering = Covering' SyntaxDesc

isCovering :: Covering' sd -> Bool
isCovering Covering = True
isCovering _ = False

isAlreadyCovered :: Covering' sd -> Bool
isAlreadyCovered AlreadyCovered = True
isAlreadyCovered _ = False

isPartiallyCovering :: Covering' sd -> Maybe ([sd], [sd])
isPartiallyCovering (PartiallyCovering p ps) = Just (p, ps)
isPartiallyCovering _ = Nothing

combine :: [(sd, Covering' sd)] -> Covering' sd
combine covs = case partition (isAlreadyCovered . snd) covs of
  (_, []) -> AlreadyCovered
  (acs, covs) -> case (acs, partition (isCovering . snd) covs) of
    ([] , (cds, []))   -> Covering
    (acs, (cds, []))   -> PartiallyCovering (map fst cds) (map fst acs)
    (acs, (cds, covs)) ->
     let (ps, pss) = unzip $ mapMaybe (isPartiallyCovering . snd) covs in
     PartiallyCovering (concat (map fst cds : ps)) $
       concat (map fst acs : pss)

-- Precondition:
--   The pattern has been elaborated against a description that
--   contains the description so it should not be possible for
--   the description to be incompatible.
--   It can at most not have enough cases to handle the pat.
-- Postcondition:
--   The output is a description corresponding to the original
--   one minus the case covered by the input pattern.
shrinkBy :: SyntaxTable -> SyntaxDesc -> Pat -> Covering
shrinkBy table = start where

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
      PartiallyCovering ((:) <$> p1 <*> p2) $ concat
        [ (:) <$> p1  <*> p2s
        , (:) <$> p1s <*> p2
        , (:) <$> p1s <*> p2s ]
    (PartiallyCovering p1 p1s, Covering) ->
      PartiallyCovering (map (: map fst ds) p1) (map (: map fst ds) p1s)
    (Covering, PartiallyCovering p2 p2s) ->
      PartiallyCovering (map (fst d :) p2) (map (fst d :) p2s)
  gos _ _ = error "Impossible"

  go :: (SyntaxDesc, VSyntaxDesc) -> Pat -> Covering
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
  go (VNilOrCons cb cb') = go VNil <> go (VCons cb cb')
  go (VBind s cb) = fmap (LamP unknown . Scope (Hide Unused)) <$> start cb
  go (VEnumOrTag ss ts) =
    let enums = map (\ s -> (pure $ AtP unknown s) :| []) ss
        tagged = ts <&> \ (s, ds) -> do
          args <- traverse start ds
          pure $ ConsP unknown (AtP unknown s) . foldr (ConsP unknown) (AtP unknown "") <$> sequence args
    in fromList (concatMap toList (enums ++ tagged))
  go VWildcard = (pure $ UnderscoreP unknown) :| []
  go (VSyntaxCat _) = (:| []) $ do
    ns <- get
    (n, ns) <- case ns of
                 (n:ns) -> pure (n, ns)
                 _ -> error "Impossible"
    put ns
    pure $ VarP unknown $ Variable unknown n
