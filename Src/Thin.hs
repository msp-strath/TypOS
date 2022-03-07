module Thin where

import Data.Bits
import Control.Monad

import GHC.Stack

import Bwd

newtype DB = DB { dbIndex :: Int }
  deriving (Show, Eq, Ord)

prd :: HasCallStack => DB -> DB
prd (DB i) | i <= 0 = error ("Took the prdecessor of DB index " ++ show i)
prd (DB i) = DB (i - 1)

scc :: DB -> DB
scc (DB i) = DB (i + 1)

data Th = Th
  { thinning :: Integer
  , bigEnd   :: Int  -- must be non-negative
  }

class Thable t where
  (*^) :: HasCallStack => t -> Th -> t

class Selable t where
  (^?) :: Th -> t -> t

instance Thable (CdB a) where
  CdB a th *^ ph = CdB a (th *^ ph)

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

instance Thable DB where
  DB i *^ th | i >= bigEnd th = error $ "Failed thinning " ++ show i ++ " by " ++ show th
  i *^ th = case thun th of
    (th, False) -> scc (i *^ th)
    (th, True) -> case i of
      DB 0 -> DB 0
      i -> scc (prd i *^ th)

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
thun :: HasCallStack => Th -> (Th, Bool)
thun (Th th i) | i <= 0 = error $ "thun with i = " ++ show i
thun (Th th i) = (Th (shiftR th 1) (i-1), testBit th 0)

instance Show Th where
  show th@(Th _ i) = "[" ++ go i th "]" where
    go 0 th = id
    go i th = go (i-1) th' . ((if b then '1' else '0'):) where
      (th', b) = thun th

(<^>) :: HasCallStack => Th -> Th -> Th
(<^>) = (*^)

-- de Bruijn index is 2^
inx :: ( DB  -- var is non-negative and strictly less than
       , Int  -- this
       )
    -> Th
inx (DB i, j) {- | 0 <= i && i < j -} = Th (bit i) j

-- th must not be 0
lsb :: Th -> DB
lsb th = case thun th of
  (_, True) -> DB 0
  (th, False) -> scc (lsb th)

thickx :: Th -> DB -> Maybe DB
thickx (Th th i) v | i <= 0 = error $ "thickx with i = " ++ show i
thickx th v = case thun th of
  (th, False) -> guard (v > DB 0) >> thickx th (prd v)
  (th, True) | v == DB 0 -> pure (DB 0)
             | otherwise -> scc <$> thickx th v

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
data CdB a = CdB a Th
  deriving (Show, Eq, Ord)

weak :: CdB a -> CdB a
weak (CdB t th) = CdB t (th -? False)

weaks :: Int -> CdB a -> CdB a
weaks i (CdB t th) = CdB t (th <> none i)

($^) :: (a -> b) -> CdB a -> CdB b
f $^ CdB a th = CdB (f a) th
  -- f better be support-preserving

scope :: CdB a -> Int
scope (CdB _ th) = bigEnd th

support :: CdB a -> Int
support (CdB _ th) = weeEnd th

-- Invariant: bigEnd th = bigEnd ph
-- The big ends of the outputs coincide at the union.
cop :: Th -> Th -> CdB (Th, Th)
cop th ph
  | bigEnd th == 0 = CdB (none 0, none 0) (none 0)
  | otherwise = case (thun th, thun ph) of
      ((th, a), (ph, b)) -> case (cop th ph, a || b) of
        (CdB c ps, False)       -> CdB c (ps -? False)
        (CdB (th, ph) ps, True) -> CdB (th -? a, ph -? b) (ps -? True)


-- fixme: avoid quadratic
-- Invariant: whole list's thinnings have bigEnd i
copz :: Bwd (CdB a) -> Int -> CdB (Bwd (CdB a))
copz B0               i = CdB B0 (none i)
copz (az :< CdB a ph) i = case copz az i of
  CdB az th -> case cop th ph of
    CdB (th, ph) ps -> CdB (fmap (*^ th) az :< CdB a ph) ps

-- relevant pairing
data RP a b = CdB a :<>: CdB b deriving (Show, Eq, Ord)
(<&>) :: CdB a -> CdB b -> CdB (RP a b)
CdB a th <&> CdB b ph = CdB (CdB a th' :<>: CdB b ph') ps where
  CdB (th', ph') ps = cop th ph
splirp :: CdB (RP a b) -> (CdB a -> CdB b -> t) -> t
splirp (CdB (CdB a th :<>: CdB b ph) ps) k =
  k (CdB a (th <^> ps)) (CdB b (ph <^> ps))

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
thickenCdB th (CdB x ph) = CdB x <$> thicken th ph

which :: (a -> Bool) -> Bwd a -> Th
which p B0 = none 0
which p (xz :< x) = which p xz -? p x

-- This is left-biased (we prioritise fitting the left's daeh)
-- [<0,1,2]   `intersection` [<0,1,2,0] === [<0,1,2]
-- [<0,1,2,0] `intersection` [<0,1,2]   === [<0]
lintersection :: Eq a => Bwd a -> Bwd a -> (Th, Bwd a, Th)
lintersection xzx@(xz :< x) yzy@(yz :< y)
  | x == y      = let (thx, xyz, thy) = lintersection xz yz in
                  (thx -? True, xyz :< x, thy -? True)
  | x `elem` yz = let (thx, xyz, thy) = lintersection xzx yz in
                  (thx, xyz, thy -? False)
  | otherwise   = let (thx, xyz, thy) = lintersection xz yzy in
                  (thx -? False, xyz, thy)
lintersection xz yz = (none (length xz), B0, none (length yz))

findSub :: Eq a => Bwd a -> Bwd a -> Maybe Th
findSub xz yz = do
  let (thx, xyz, thy) = lintersection xz yz
  guard (is1s thx)
  pure thy

-- | Replace the most local 1 in a thinning with 0
---     th = 0000110[1]00000
--- pop th = 0000110[0]00000
pop :: Th -> Th
pop th
   | weeEnd th <= 0 = error "pop'd an empty thinning"
   | otherwise = (ones (weeEnd th - 1) -? False) <^> th
