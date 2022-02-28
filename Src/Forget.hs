module Forget where

class Forget a b where
  forget :: a -> b

instance Forget a () where
  forget _ = ()
