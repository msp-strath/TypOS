{-# LANGUAGE DeriveTraversable, ScopedTypeVariables #-}

{-|
Description: snoc lists
-}
module Bwd where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Control.Monad.State

data Bwd x = B0 | Bwd x :< x
  deriving (Show, Eq, Functor, Foldable, Traversable)
infixl 4 :<

instance Semigroup (Bwd x) where
  xz <> B0        = xz
  xz <> (yz :< y) = xz <> yz :< y

instance Monoid (Bwd x) where
  mempty = B0

-- | lookup with a more convenient name
(<!) :: Bwd x -> Int -> x
(_  :< x) <! 0 = x
(xs :< _) <! n = xs <! (n - 1)

infixl 4 <><

-- | append a list onto a snoc list, giving a snoc list,
-- reversing the list as it goes
(<><) :: Bwd x -> [x] -> Bwd x
xz <>< [] = xz
xz <>< (x : xs) = (xz :< x) <>< xs

-- | put a snoc list onto the head of a list, giving a list
(<>>) ::  Bwd x -> [x] -> [x]
B0 <>> xs = xs
(xz :< x) <>> xs = xz <>> (x:xs)

-- | mapzss f b l is equivalent to (fmap f b) <>> l
-- but hand-coded to do it in a single pass and does not
-- traverse the list.
mapzss :: (a -> b) -> Bwd a -> [b] -> [b]
mapzss f B0 xs = xs
mapzss f (xz :< x) xs = mapzss f xz (f x : xs)

-- | Equivalent to (fmap f xz) <>> [], but in one pass
mapzs :: (a -> b) -> Bwd a -> [b]
mapzs f xz = mapzss f xz []

-- | Treat a snoc list as a stack and returns the top.
-- Warning: incomplete pattern match.
top :: Bwd x -> x
top (_ :< x) = x

-- | 'takez' is 'take' but renamed so 'take' can still be used
takez :: Bwd x -> Int -> Bwd x
takez _ 0 = B0
takez (xz :< x) w = takez xz (w-1) :< x

-- | 'dropz' is 'drop' but renamed so 'drop' can still be used
dropz :: Bwd x -> Int -> Bwd x
dropz xz 0 = xz
dropz (xz :< x) w = dropz xz (w-1)

-- | singleton snoc list
singleton :: x -> Bwd x
singleton x = B0 :< x

-- | matches 'only' singleton, and will fail in not-nice ways otherwise
only :: Bwd x -> x
only (B0 :< x) = x

-- | 'focusBy' takes a predicate p and a snoc list, and returns
-- a pointed cursor into that snoc for the first item that satisfies p
-- (or Nothing otherwise).
focusBy :: (x -> Maybe y) -> Bwd x -> Maybe (Bwd x, y, [x])
focusBy p xz = go xz [] where

  go B0        xs = Nothing
  go (xz :< x) xs
    | Just y <- p x = pure (xz, y, xs)
    | otherwise     = go xz (x : xs)

-- | 'focus' specializes 'focusBy' to equality with the given element
focus :: Eq x => x -> Bwd x -> Maybe (Bwd x, x, [x])
focus x = focusBy (\ y -> y <$ guard (x == y))

-- | "curl up" n items from the snoc part onto the list part
curl :: Int -> (Bwd x, [x]) -> (Bwd x, [x])
curl 0 xzs = xzs
curl n (xz :< x, xs) = curl (n-1) (xz, x : xs)

-- | A 'Cursor' is a location in a list (or a snoc list)
-- Note that it can point to the head or tail, it does not
-- points to an element location.
data Cursor x
  = Bwd x :<+>: [x]
  deriving (Eq, Foldable, Functor, Show, Traversable)
infixl 3 :<+>:

-- | Each value of type `x` induces its own space of
--   de Bruijn indices. This function tags each value
--   with the corresponding index.
--
--   deBruijnify (B0 :< "x" :< "y" :< "x")
--   == B0 :< ("x",1) :< ("y",0) :< ("x",0)
deBruijnify :: forall x. Ord x => Bwd x -> Bwd (x, Int)
deBruijnify xz = go xz `evalState` Map.empty where

  new :: x -> State (Map x Int) Int
  new x = do
    st <- get
    let n = fromMaybe 0 (Map.lookup x st)
    put (Map.insert x (n + 1) st)
    pure n

  go :: Bwd x -> State (Map x Int) (Bwd (x, Int))
  go B0 = pure B0
  go (xz :< x) = do
    n <- new x
    xnz <- go xz
    pure (xnz :< (x, n))

-- | 'groupBy' for snoc lists
groupBy :: (a -> a -> Bool) -> Bwd a -> Bwd (Bwd a)
groupBy eq B0 = B0
groupBy eq (xz :< x) = go [x] x xz where

  go acc x (yz :< y) | eq x y = go (y : acc) x yz
  go acc _ yz = groupBy eq yz :< (B0 <>< acc)

-- | 'nub' for snoc lists
nub :: Eq a => Bwd a -> Bwd a
nub = go [] where
  go acc B0 = B0
  go acc (xs :< x)
    | x `elem` acc = go acc xs
    | otherwise = go (x : acc) xs :< x

-- | 'unzipWith' for snoc lists
unzipWith :: (a -> (b, c)) -> Bwd a -> (Bwd b, Bwd c)
unzipWith f B0 = (B0, B0)
unzipWith f (az :< a) =
  let (bz, cz) = unzipWith f az in
  let (b, c) = f a in
  (bz :< b, cz :< c)
