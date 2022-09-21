{-|
Description: for forgetting information about a structure. Basically a generalized projection.
-}
module Forget where

-- | Class Forget says that one can 'project out' something of type b from something of type a.
class Forget a b where
  forget :: a -> b

-- | We can always forget everything
instance Forget a () where
  forget _ = ()
