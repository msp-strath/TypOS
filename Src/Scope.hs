module Scope where

import Hide
import Thin

-- TODO: refactor Tm using Scope?
data Scope x t = Scope (Hide x) t
  deriving (Eq, Show)

boundName :: Scope x t -> x
boundName (Scope (Hide x) _) = x

instance Thable t => Thable (Scope x t) where
  Scope x t *^ th = Scope x (t *^ (th -? True))
