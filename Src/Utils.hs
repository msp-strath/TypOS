module Utils where

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
