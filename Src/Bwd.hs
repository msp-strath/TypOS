{-# LANGUAGE DeriveTraversable #-}

module Bwd where

data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Functor, Foldable, Traversable)
infixl 6 :<

instance Monoid (Bwd x) where
  mempty = B0
  mappend xz B0        = xz
  mappend xz (yz :< y) = mappend xz yz :< y

instance Semigroup (Bwd x) where (<>) = mappend

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

only :: Bwd x -> x
only (B0 :< x) = x

curl :: Int -> (Bwd x, [x]) -> (Bwd x, [x])
curl 0 xzs = xzs
curl n (xz :< x, xs) = curl (n-1) (xz, x : xs)