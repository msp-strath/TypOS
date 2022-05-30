{-# OPTIONS_GHC -Wno-unused-imports #-}
module Term (module Term, module Term.Base, module Term.Substitution{-, Term.Mangler-}) where

import Term.Base
import Term.Substitution hiding (expand)
-- import Term.Mangler
