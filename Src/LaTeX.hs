{-# LANGUAGE OverloadedStrings #-}

module LaTeX where

import Concrete.Base
import Doc
import Syntax (SyntaxDesc, expand)

class LaTeX a where
  type Format a
  toLaTeX :: Format a -> a -> Doc ()

call :: Doc () -> [Doc ()] -> Doc ()
call d [] = d
call d (x : xs) = call (d <> braces x) xs

instance LaTeX Variable where
  type Format Variable = ()
  toLaTeX _ (Variable str) = text str

instance LaTeX Atom where
  type Format Atom = ()
  toLaTeX _ str = text str

instance LaTeX Raw where
  type Format Raw = SyntaxDesc
  toLaTeX d = \case
    Var v -> toLaTeX v
    At a -> case expand d of
      vd -> _ -- call "typosAtom" [toLaTeX a]
    Cons p q -> case d of
      _ -> _
    Lam sc -> _wd
    Sbst bwd raw -> _we
