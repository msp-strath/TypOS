{-# LANGUAGE GADTs #-}
module Vector where

import Data.Kind

data Nat = Z | S Nat

infixr 5 :*
data Vector (n :: Nat) (a :: Type) where
  V0 :: Vector Z a
  (:*) :: a -> Vector n a -> Vector (S n) a

hd :: Vector (S n) a -> a
hd (t :* _) = t

instance Functor (Vector n) where
  fmap f V0 = V0
  fmap f (x :* xs) = f x :* fmap f xs
