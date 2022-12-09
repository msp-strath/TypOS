module Scope where
{- Description: Defining 'Scope'. A scope is a pair of a hidden value (a bound name) in a "term"
 -}

import Hide (Hide(unhide))
import Thin (Thable(..), (-?))

-- TODO: refactor Tm using Scope?
-- | Definition of Scope
data Scope x t = Scope (Hide x) t
  deriving (Eq, Show)

-- | extract the bound name from a 'Scope'
boundName :: Scope x t -> x
boundName (Scope x _) = unhide x

-- | Scopes are thinable (by adding a bit at the end)
instance Thable t => Thable (Scope x t) where
  Scope x t *^ th = Scope x (t *^ (th -? True))
