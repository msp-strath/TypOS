{-# LANGUAGE DeriveTraversable, ScopedTypeVariables #-}

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

(<!) :: Bwd x -> Int -> x
(_  :< x) <! 0 = x
(xs :< _) <! n = xs <! (n - 1)

infixl 4 <><

(<><) :: Bwd x -> [x] -> Bwd x
xz <>< [] = xz
xz <>< (x : xs) = (xz :< x) <>< xs

(<>>) ::  Bwd x -> [x] -> [x]
B0 <>> xs = xs
(xz :< x) <>> xs = xz <>> (x:xs)

mapzss :: (a -> b) -> Bwd a -> [b] -> [b]
mapzss f B0 xs = xs
mapzss f (xz :< x) xs = mapzss f xz (f x : xs)

mapzs :: (a -> b) -> Bwd a -> [b]
mapzs f xz = mapzss f xz []

bwdProj :: Bwd x -> Int -> x
bwdProj (xz :< x) 0 = x
bwdProj (xz :< x) n = bwdProj xz (n-1)

top :: Bwd x -> x
top (xz :< x) = x

dropz :: Bwd x -> Int -> Bwd x
dropz xz 0 = xz
dropz (xz :< x) w = dropz xz (w-1)

singleton :: x -> Bwd x
singleton x = B0 :< x

only :: Bwd x -> x
only (B0 :< x) = x

focusBy :: (x -> Maybe y) -> Bwd x -> Maybe (Bwd x, y, [x])
focusBy p xz = go xz [] where

  go B0        xs = Nothing
  go (xz :< x) xs
    | Just y <- p x = pure (xz, y, xs)
    | otherwise     = go xz (x : xs)

focus :: Eq x => x -> Bwd x -> Maybe (Bwd x, x, [x])
focus x = focusBy (\ y -> y <$ guard (x == y))

curl :: Int -> (Bwd x, [x]) -> (Bwd x, [x])
curl 0 xzs = xzs
curl n (xz :< x, xs) = curl (n-1) (xz, x : xs)

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

groupBy :: (a -> a -> Bool) -> Bwd a -> Bwd (Bwd a)
groupBy eq B0 = B0
groupBy eq (xz :< x) = go [x] x xz where

  go acc x (yz :< y) | eq x y = go (y : acc) x yz
  go acc _ yz = groupBy eq yz :< (B0 <>< acc)
