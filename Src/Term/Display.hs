{-# LANGUAGE ConstraintKinds #-}

module Term.Display where

import Display
import Term
import Thin
import Unelaboration.Monad

instance (Show m, UnelabMeta m) => Display (Tm m) where
  type DisplayEnv (Tm m) = Naming
  display = viaPretty

instance Display Meta where
  type DisplayEnv Meta = ()
  display= viaPretty

instance (Show m, UnelabMeta m) => Display (CdB (Tm m)) where
  type DisplayEnv (CdB (Tm m)) = Naming
  display = viaPretty

instance (Show m, UnelabMeta m) => Display (Sbst m) where
  type DisplayEnv (Sbst m) = Naming
  display = viaPretty
