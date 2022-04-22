{-# LANGUAGE DeriveTraversable #-}

module Hide where

newtype Hide x = Hide {unhide :: x}
  deriving (Functor)
instance Show (Hide x) where show _ = ""
instance Eq   (Hide x) where _ == _ = True
instance Ord  (Hide x) where compare _ _ = EQ

data Named a = Hide String := a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
