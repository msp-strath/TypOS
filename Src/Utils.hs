module Utils where

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State

isAllJustBy :: [a] -> (a -> Maybe b) -> Either a [b]
isAllJustBy [] f = pure []
isAllJustBy (a:as) f = do
  b <- maybe (Left a) Right (f a)
  bs <- isAllJustBy as f
  pure (b:bs)

isAll :: (a -> Bool) -> [a] -> Either a ()
isAll p [] = pure ()
isAll p (x:xs) = do
  if p x then pure () else Left x
  isAll p xs

whenLeft :: Applicative m => Either a b -> (a -> m ()) -> m ()
whenLeft (Left a) k = k a
whenLeft (Right _) k = pure ()

whenNothing :: Applicative m => Maybe a -> m () -> m ()
whenNothing Nothing k = k
whenNothing (Just _) k = pure ()

whenJust :: Applicative m => Maybe a -> (a -> m ()) -> m ()
whenJust Nothing k = pure ()
whenJust (Just a) k = k a

whenM :: Monad m => m Bool -> m () -> m ()
whenM cond m = cond >>= flip when m

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM cond m = cond >>= flip unless m

instance Semigroup m => Semigroup (State s m) where
  (<>) = liftM2 (<>)

instance Monoid m => Monoid (State s m) where
  mempty = pure mempty

class HalfZip f where
  halfZip :: f x -> f y -> Maybe (f (x, y))

instance HalfZip [] where
  halfZip [] [] = Just []
  halfZip (x:xs) (y:ys) = ((x,y):) <$> halfZip xs ys
  halfZip _ _ = Nothing

allUnique :: (Ord a, Foldable f) => f a -> Either a (Set a)
allUnique = flip foldr (pure Set.empty) $ \ a acc -> do
  s <- acc
  if a `Set.member` s then Left a else Right (Set.insert a s)

