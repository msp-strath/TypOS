module Thin where

import Data.Bits
import Control.Monad

import Bwd

data Th = Th
  { thinning :: Integer
  , bigEnd   :: Int  -- must be non-negative
  }

class Thable t where
  (*^) :: t -> Th -> t

class Selable t where
  (^?) :: Th -> t -> t

instance Thable (CdB a) where
  (a, th) *^ ph = (a, th *^ ph)

{-
thinning composition is diagrammatic
good luck enforcing composability!

              o
       o----->o
o----->o----->o
       o----->o
              o
o----->o----->o
-}

instance Thable Th where
  _  *^ Th _  0 = none 0
  th *^ ph = case thun ph of
    (ph, False) -> (th *^ ph) -? False
    (ph, True)  -> case thun th of
      (th, b) -> (th *^ ph) -? b

instance Selable Th where
  (^?) = (*^)

instance Thable Int where
  i *^ th | i >= bigEnd th = error $ "Failed thinning " ++ show i ++ " by " ++ show th
  i *^ th = case thun th of
    (th, False) -> 1 + (i *^ th)
    (th, True) -> case i of
      0 -> 0
      i -> 1 + ((i - 1) *^ th)

-- 2^(i-1), which is a remarkably well behaved thing
full :: Bits a => Int -> a
full i = xor (shiftL ones i) ones where ones = complement zeroBits

instance Eq Th where
  Th th i == Th ph j = (i == j) && ((th .&. full i) == (ph .&. full j))

instance Ord Th where
  compare (Th th i) (Th ph j) = compare (i, th .&. full i) (j, ph .&. full j)

weeEnd :: Th -> Int
weeEnd (Th th i) = popCount (th .&. full i)

ones, none :: Int -> Th
ones i = Th (full i) i
none i = Th 0 i

is0s, is1s :: Th -> Bool
is0s th = th == none (bigEnd th)
is1s th = th == ones (bigEnd th)

-- snoc for bits
(-?) :: Th -> Bool -> Th
Th th i -? b = Th (go b) (i+1) where
  th' = shiftL th 1
  go True  = th' .|. bit 0
  go False = th'

-- inverts snoc
thun :: Th -> (Th, Bool)
thun (Th th i) | i <= 0 = error $ "thun with i = " ++ show i
thun (Th th i) = (Th (shiftR th 1) (i-1), testBit th 0)

instance Show Th where
  show th@(Th _ i) = "[" ++ go i th "]" where
    go 0 th = id
    go i th = go (i-1) th' . ((if b then '1' else '0'):) where
      (th', b) = thun th

(<^>) :: Th -> Th -> Th
(<^>) = (*^)

-- de Bruijn index is 2^
inx :: ( Int  -- var is non-negative and strictly less than
       , Int  -- this
       )
    -> Th
inx (i, j) {- | 0 <= i && i < j -} = Th (bit i) j

-- th must not be 0
lsb :: Th -> Int
lsb th = case thun th of
  (_, True) -> 0
  (th, False) -> 1 + lsb th

-- thin a deBruijn index represented as a bounded number,
-- not as a singleton Thinning
-- saves us inx-ing, composing, then lsb-ing
thinx :: Int -> Th -> Int
thinx = (*^)

-- invert selection
comp :: Th -> Th
comp (Th th i) = Th (xor th (full i)) i

-- kind of append, only taking first i bits of second arg into account
instance Monoid Th where
  mempty = ones 0
  mappend (Th th j) (Th ph i) = Th (shiftL th i .|. (ph .&. full i)) (i+j)
instance Semigroup Th where (<>) = mappend

-- "take" for bits, undoes mappend
thChop :: Th -> Int -> (Th, Th)
thChop (Th th i) j = (Th (shiftR th j) (i-j), Th (th .&. full j) j)

-- "take" from the wee end
chopTh :: Int -> Th -> (Th, Th)
chopTh 0 th = (th, ones 0)
chopTh w th = case thun th of
  (th, True)  -> chopTh (w-1) th <> (ones 0, ones 1)
  (th, False) -> chopTh w     th <> (ones 0, none 1)

-- codeBruijn things are paired with a thinning
-- from support to scope
type CdB a = (a, Th)

weak :: CdB a -> CdB a
weak (t, th) = (t, th -? False)

weaks :: Int -> CdB a -> CdB a
weaks i (t, th) = (t, th <> none i)

($^) :: (a -> b) -> CdB a -> CdB b
f $^ (a, th) = (f a, th)
  -- f better be support-preserving

scope :: CdB a -> Int
scope (_, th) = bigEnd th

support :: CdB a -> Int
support (_, th) = weeEnd th

-- Invariant: bigEnd th = bigEnd ph
-- The big ends of the outputs coincide at the union.
cop :: Th -> Th -> CdB (Th, Th)
cop th ph
  | bigEnd th == 0 = ((none 0, none 0), none 0)
  | otherwise = case (thun th, thun ph) of
      ((th, a), (ph, b)) -> case (cop th ph, a || b) of
        ((c, ps), False)       -> (c , ps -? False)
        (((th, ph), ps), True) -> ((th -? a, ph -? b), ps -? True)


-- fixme: avoid quadratic
-- Invariant: whole list's thinnings have bigEnd i
copz :: Bwd (CdB a) -> Int -> CdB (Bwd (CdB a))
copz B0              i = (B0, none i)
copz (az :< (a, ph)) i = case copz az i of
  (az, th) -> case cop th ph of
    ((th, ph), ps) -> (fmap (*^ th) az :< (a, ph), ps)

-- relevant pairing
data RP a b = CdB a :<>: CdB b deriving (Show, Eq, Ord)
(<&>) :: CdB a -> CdB b -> CdB (RP a b)
(a, th) <&> (b, ph) = ((a, th') :<>: (b, ph'), ps) where
  ((th', ph'), ps) = cop th ph
splirp :: CdB (RP a b) -> (CdB a -> CdB b -> t) -> t
splirp ((a, th) :<>: (b, ph), ps) k =
  k (a, th <^> ps) (b, ph <^> ps)

instance Selable (Bwd x) where
  th ^? B0 = B0
  th ^? (xz :< x) = case thun th of
    (th, b) -> (if b then (:< x) else id) (th ^? xz)

(?<) :: Th -> Bwd x -> Bwd x
(?<) = (^?)

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


-- pullback th ph = (th*ph, ps, ph*th)
--   o--th*ph-->o
--   |\__       |
--   |   \      |
-- ph*th  ps   th
--   |      \__ |
--   |         vv
--   o---ph---->o
-- Note: invariant that bigEnd th == bigEnd ph
pullback :: Th -> Th -> (Th, Th, Th)
pullback th ph
  | bigEnd th == 0 = (none 0, none 0, none 0)
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

-- thicken th ph computes ps such that ps <^> th = ph
-- i.e., th is "what's allowed" and ph is "what's required"
-- ps is the witness that everything required is allowed
thicken :: Th -> Th -> Maybe Th
thicken th ph = ps <$ guard (is1s th')
  where
  (ps, _, th') = pullback th ph

thickenCdB :: Th -> CdB a -> Maybe (CdB a)
thickenCdB th (x, ph) = (x,) <$> thicken th ph

which :: (a -> Bool) -> Bwd a -> Th
which p B0 = none 0
which p (xz :< x) = which p xz -? p x

findSub :: Eq a => Bwd a -> Bwd a -> Th
findSub aza@(az :< a) (bz :< b)
  | a == b    = findSub az  bz -? True
  | otherwise = findSub aza bz -? False
findSub _ bz = none (length bz)
