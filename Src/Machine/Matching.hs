{-# LANGUAGE OverloadedStrings #-}

module Machine.Matching where

import Data.Bifunctor

import Bwd
import Vector
import Actor
import Thin
import Term.Base
import Term.Display()
import Hide
import Pattern (Pat'(..))
import Pretty (Pretty(..))

{-
import Display (unsafeDisplayClosed)
import Debug.Trace
import Options (unsafeOptions)
-}

data Failure
  = DontKnow --Meta
  | Mismatch
  deriving (Show)

instance Pretty Failure where
  pretty DontKnow = "Don't Know" -- <+> pretty meta
  pretty Mismatch = "Mismatch"

data Problem = Problem
  { localBinders :: Bwd String -- binders we have gone under
  , problemPat :: Pat          -- pattern to match
  , problemTerm :: Term        -- candidate term
  }

-- Only use this to debug clauses
mismatch :: Pat -> Term -> Failure
mismatch _ _ = Mismatch
--mismatch p t = trace (unsafeDisplayClosed unsafeOptions p ++ " ∌ " ++ unsafeDisplayClosed unsafeOptions t) Mismatch

stuck :: Xn m -> Bool
stuck (_ :$: _) = True
stuck (_ :-: _) = True
stuck (GX _ _)  = True
stuck _         = False

type Matching = ([(ActorMeta, ([String], Term))], [(String, Hide String)])

match :: (Term -> Term) -- head normal former
      -> Problem
      -> ( Term -- reduced version of the terms in the input problems
         , Either Failure Matching)
match hnf p = first hd $ matchN hnf mempty (p :* V0)

matchN :: (Term -> Term) -- head normal former
       -> Matching
       -> Vector n Problem
       -> ( Vector n Term -- reduced version of the terms in the input problems
          , Either Failure Matching)
matchN hnf mat V0 = (V0, pure mat)
matchN hnf mat (Problem zx (AT x p) tm :* xs)
  = let mat' =  first ((x, (zx <>> [], tm)) :) mat in
    matchN hnf mat' (Problem zx p tm :* xs)
matchN hnf mat (Problem zx (MP x ph) tm@(CdB _ th) :* xs)
  | is1s ph -- common easy special case, essentially x@_
  = let mat' = first ((x, (zx <>> [], tm)) :) mat in
    first (tm:*) $ matchN hnf mat' xs
  | otherwise
  = let g = bigEnd th - bigEnd ph in
  -- we can do better:
  -- t may not depend on disallowed things until definitions are expanded
    case instThicken hnf (ones g <> ph) tm of
      (tm, Right thickened) ->
        let mat' = first ((x, ((ph ?< zx) <>> [], thickened)) :) mat in
        first (tm:*) $ matchN hnf mat' xs
      (tm, Left err) -> (tm :* fmap problemTerm xs, Left err)
matchN hnf mat (Problem zx pat tm :* xs) = let tmnf = hnf tm in case (pat, expand tmnf) of
  (HP, _) -> first (tmnf:*) $ matchN hnf mat xs
  (GP, _) -> (tmnf :* fmap problemTerm xs, Left (mismatch pat tmnf))
  (_, t) | stuck t -> case matchN hnf mat xs of
    (tms, err@(Left Mismatch)) -> (tmnf :* tms, err)
    (tms, _) -> (tmnf:*tms, Left DontKnow)
  (VP i, VX j _) | i == j -> first (tmnf:*) $ matchN hnf mat xs
  (AP a, AX b _) | a == b -> first (tmnf:*) $ matchN hnf mat xs
  (PP p q, s :%: t) -> case matchN hnf mat (Problem zx p s :* Problem zx q t :* xs) of
    (s :* t :* tms, res) -> ((s % t) :* tms, res)
  (BP (Hide x) p, y :.: t) ->
    let mat' =  second ((x, Hide y) :) mat in
    case matchN hnf mat' (Problem (zx :< x) p t :* xs) of
      (b :* tms, res) -> ((y \\ b) :* tms, res)
  _ -> (tmnf :* fmap problemTerm xs, Left (mismatch pat tmnf))

instThicken :: (Term -> Term) -> Th -> Term
            -> (Term, Either Failure Term)
instThicken hnf ph t = let tmnf = hnf t in case tmnf of
  v@(CdB V _) -> case thickenCdB ph v of
    Just v -> (tmnf, pure v)
    Nothing -> (tmnf, Left Mismatch)
  m@(CdB (meta :$ _) _) -> case thickenCdB ph m of
    Just m -> (tmnf, pure m)
    Nothing -> (tmnf, Left DontKnow)
  x -> case expand x of
    AX a ga -> (tmnf, pure (atom a (weeEnd ph)))
    s :%: t -> case instThicken hnf ph s of
      (s, Left Mismatch) -> (s % t, Left Mismatch)
      (s, ress) -> case instThicken hnf ph t of
        (t, Left Mismatch) -> (s % t, Left Mismatch)
        (t, rest) -> (s % t, (%) <$> ress <*> rest)
    (x :.: t) -> case instThicken hnf (ph -? True) t of
      (b, resb) -> (x \\ b, (x \\) <$> resb)
