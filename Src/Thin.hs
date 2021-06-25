module Thin where

import Data.Bits
import Control.Arrow

import Bwd

newtype Th = Th Integer deriving Eq

ones, none :: Th
ones = Th (negate 1)
none = Th 0

-- snoc for bits
(-?) :: Th -> Bool -> Th
Th th -? b = Th (go b) where
  th' = shiftL th 1
  go True  = th' .|. bit 0
  go False = th'

-- inverts snoc
thun :: Th -> (Th, Bool)
thun (Th th) = (Th (shiftR th 1), testBit th 0)

instance Show Th where
  show th
    | th == none = "+0"
    | th == ones = "-1"
    | otherwise = case thun th of
      (th, b) -> show th ++ if b then "1" else "0"

-- de Bruijn index is 2^
inx :: Int -> Th
inx i = Th (bit i)


-- th must not be 0
lsb :: Th -> Int
lsb th = case thun th of
  (_, True) -> 0
  (th, False) -> 1 + lsb th

-- invert selection
comp :: Th -> Th
comp (Th th) = Th (complement th)

-- "take" for bits
thChop :: Th -> Int -> (Th, Th)
thChop (Th th) i = (Th (shiftR th i), Th (th .&. full i))

-- 2^(i-1), which is a remarkably well behaved thing
full :: Bits a => Int -> a
full i = xor (shiftL ones i) ones where ones = complement zeroBits

-- kind of append, only taking first i bits of second arg into account
apth :: Th -> (Int, Th) -> Th
apth (Th th) (i, Th ph) = Th (shiftL th i .|. (ph .&. full i))

-- codeBruijn things are paired with a thinning
-- from support to scope
type CdB a = (a, Th)

weak :: CdB a -> CdB a
weak (t, th) = (t, th -? False)

(*^) :: CdB a -> Th -> CdB a
(a, th) *^ ph = (a, th <> ph)

instance Monoid Th where
  mempty = ones
  mappend th ph
    | th == none = none
    | ph == none = none
    | th == ones = ph
    | ph == ones = th
    | otherwise = case thun ph of
      (ph, False) -> mappend th ph -? False
      (ph, True)  -> case thun th of
        (th, b) -> mappend th ph -? b

instance Semigroup Th where (<>) = mappend

cop :: Th -> Th -> CdB (Th, Th)
cop th ph
  | th == ones = ((ones, ph), ones)
  | ph == ones = ((th, ones), ones)
  | th == none && ph == none = ((none, none), none)
  | otherwise = case (thun th, thun ph) of
      ((th, a), (ph, b)) -> case (cop th ph, a || b) of
        ((c, ps), False)       -> (c , ps -? False)
        (((th, ph), ps), True) -> ((th -? a, ph -? b), ps -? True)

-- (iz, th) and (jz, ph) are images for some of a scope
-- compute a merge of iz and jz which are images for
-- the union of th and ph
riffle :: (Bwd a, Th) -> (Bwd a, Th) -> Bwd a
riffle (B0, _) (jz, _) = jz
riffle (iz :< i, th) (jz, ph) = case thun th of
  (th, True) -> case (jz, thun ph) of
    (jz :< _, (ph, True)) -> riffle (iz, th) (jz, ph) :< i
    (jz, (ph, False))     -> riffle (iz, th) (jz, ph) :< i
  (th, False) -> case (jz, thun ph) of
    (jz :< j, (ph, True)) -> riffle (iz, th) (jz, ph) :< j
    (jz, (ph, False))     -> riffle (iz, th) (jz, ph)

-- fixme: avoid quadratic
copz :: Bwd (CdB a) -> CdB (Bwd (CdB a))
copz B0 = (B0, none)
copz (az :< (a, ph)) = case copz az of
  (az, th) -> case cop th ph of
    ((th, ph), ps) -> (fmap (*^ th) az :< (a, ph), ps)

(?<) :: Th -> Bwd x -> Bwd x
th ?< xz
  | th == none = B0
  | th == ones = xz
  | otherwise = case xz of
    B0 -> B0
    xz :< x -> case thun th of
      (th, b) -> (if b then (:< x) else id) (th ?< xz)

-- pullback th ph = (th*ph, ps, ph*th)
--   o--th*ph-->o
--   |\__       |
--   |   \      |
-- ph*th ps    th
--   |      \__ |
--   |         vv
--   o---ph---->o
pullback :: Th -> Th -> (Th, Th, Th)
pullback th ph
  | th == ones = (ph, ph, ones)
  | ph == ones = (ones, th, th)
  | th == none || ph == none = (none, none, none)
  | otherwise = case (thun th, thun ph) of
      ((th, a), (ph, b)) -> case (pullback th ph, a, b) of
        ((th', ps, ph'), False, False) ->
          (th', ps -? False, ph')
        ((th', ps, ph'), False, True) ->
          (th', ps -? False, ph' -? False)
        ((th', ps, ph'), True, False) ->
          (th' -? False, ps -? False, ph')
        ((th', ps, ph'), True, True) ->
          (th' -? True, ps -? True, ph' -? True)
