{-# LANGUAGE DeriveTraversable #-}

{-|
Description: Hiding a value by making it behave like a singleton
-}

module Hide where

-- | Hide adds a layer above a value that lets us make it look
-- like a singleton, but not forget the actual value.
newtype Hide x = Hide {unhide :: x}
  deriving (Functor)
instance Show (Hide x) where show _ = ""
instance Eq   (Hide x) where _ == _ = True
instance Ord  (Hide x) where compare _ _ = EQ

-- | Something is a 'Named' value of type 'a' if it is a pair of a
-- hidden String and a value of type 'a'. The value part is completely
-- transparent, i.e. treats the (hidden) string as an annotation.
data Named a = Hide String := a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
