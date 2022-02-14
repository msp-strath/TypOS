module Scope where

import Hide
import Thin

-- TODO: refactor Tm using Scope?
data Scope t = Scope (Hide String) t
  deriving (Eq, Show)

boundName :: Scope t -> String
boundName (Scope (Hide x) _) = x

instance Thable t => Thable (Scope t) where
  Scope x t *^ th = Scope x (t *^ (th -? True))
