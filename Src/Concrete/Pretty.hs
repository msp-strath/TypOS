{-# LANGUAGE OverloadedStrings #-}

module Concrete.Pretty where

import Data.Foldable
import Data.List

import Bwd
import Concrete.Base
import Doc
import Doc.Render.Terminal
import Format
import Hide
import Scope
import Pretty

instance Pretty (Hide String) where
  pretty (Hide x) = pretty x

instance Pretty Variable where
  pretty (Variable v) = pretty v

instance Pretty Raw where
  pretty = \case
    Var v -> pretty v
    At [] -> "[]"
    At at -> squote <> pretty at
    Cons p q -> brackets $ sep (pretty p : prettyCdr q)
    Lam (Scope x t) -> backslash <> pretty x <> dot <+> pretty t
    Sbst B0 t -> pretty t
    Sbst sg t -> hsep [ pretty sg, pretty t ]

instance Pretty (Bwd SbstC) where
  pretty sg = braces (hsepBy "," $ pretty <$> sg <>> [])

prettyCdr :: Raw -> [Doc Annotations]
prettyCdr = \case
  At [] -> []
  Cons p q -> pretty p : prettyCdr q
  p -> [pipe, pretty p]

instance Pretty SbstC where
  pretty = \case
    Keep x -> pretty x
    Drop x -> pretty x <> "*"
    Assign x t -> pretty x <> equal <> pretty t

instance Pretty ThDirective where
  pretty = \case
    ThKeep -> ""
    ThDrop -> "*"

instance Pretty RawP where
  prettyPrec d = \case
    VarP v -> pretty v
    AtP "" -> "[]"
    AtP at -> squote <> pretty at
    ConsP p q -> brackets $ sep (pretty p : prettyCdrP q)
    LamP (Scope x p) -> backslash <> pretty x <> dot <+> pretty p
    ThP (thxz, thd) p -> braces (hsep (pretty <$> thxz <>> []) <> pretty thd) <+> pretty p
    UnderscoreP -> "_"

prettyCdrP :: RawP -> [Doc Annotations]
prettyCdrP = \case
  AtP [] -> []
  ConsP p q -> pretty p : prettyCdrP q
  p -> [pipe, pretty p]

instance Pretty Actor where
  prettyPrec d = \case
    a :|: b -> parenthesise (d > 0) $ hsep [ prettyPrec 1 a, pipe, pretty b ]
    Spawn jd p a -> fold [ pretty jd, "@", pretty p, dot, space, prettyPrec 1 a ]
    Send ch t a -> fold [ pretty ch, "!", pretty t, dot, space, prettyPrec 1 a ]
    Recv ch (av, a) -> fold [ pretty ch, "?", pretty av, dot, space, prettyPrec 1 a ]
    FreshMeta syn (av, a) -> fold [ pretty syn, "?", pretty av, dot, space, prettyPrec 1 a ]
    Under (Scope x a) -> fold [ backslash , pretty x, dot, colon, prettyPrec 1 a ]
    Match tm pts -> hsep [ keyword "case", pretty tm, braces (sep $ intersperse ";" $ map pretty pts) ]
    Constrain s t -> hsep [ pretty s, "~", pretty t ]
    Push jd (x, t) a -> hsep [ pretty jd, braces (hsep [ pretty x, "->", pretty t ]) <+> dot, prettyPrec 1 a]
    Lookup tm (av, a) b -> hsep
      [ keyword "lookup", pretty tm
      , braces (hsep [ pretty av, "->", pretty a ])
      , keyword "else", prettyPrec 1 a ]
    Win -> ""
    Fail fmt -> "#" <> pretty fmt
    Print [TermPart Instantiate tm] a -> hsep [ keyword "PRINT", pretty tm, ".", prettyPrec 1 a]
    Print fmt a -> hsep [ keyword "PRINTF", pretty fmt, ".", prettyPrec 1 a]
    Break fmt a -> hsep [ keyword "BREAK", pretty fmt, ".", prettyPrec 1 a]

instance Pretty Debug where
  pretty = \case
    ShowEnv -> "%e"
    ShowStack -> "%S"
    ShowStore -> "%m"

instance Pretty Directive where
  pretty = \case
    Raw -> "%r"
    Instantiate -> "%i"
    ShowT -> "%s"

instance Pretty t => Pretty [Format Directive Debug t] where
  pretty = go B0 B0 where

    go fmt args [] = hsep ((dquote <> fold fmt <> dquote) : args <>> [])
    go fmt args (f:fs) = case f of
      TermPart d t -> go (fmt :< pretty d) (args :< pretty t) fs
      DebugPart dbg -> go (fmt :< pretty dbg) args fs
      StringPart str -> go (fmt :< pretty (escape str)) args fs

instance Pretty t => Pretty [Format () (Doc Annotations) t] where
  pretty = go mempty where

    go acc [] = acc
    go acc (f:fs) = case f of
      TermPart () t -> go (acc <> pretty t) fs
      DebugPart dbg -> go (acc <> dbg) fs
      StringPart str -> go' acc str fs

    go' acc str fs = case span ('\n' /=) str of
      (str, []) -> go (acc <> text str) fs
      (str, _:rest) -> go' (flush (acc <> text str)) rest fs


instance Pretty (RawP, Actor) where
  pretty (p, a) = hsep [ pretty p, "->", pretty a ]

instance Pretty Mode where
  pretty Input = "?"
  pretty Output = "!"

instance Pretty t => Pretty (Protocol t) where
  pretty = foldMap $ \ (m, d) -> fold [pretty m, pretty d, ". "]

instance Pretty t => Pretty (JudgementStack t) where
  pretty stk = hsep [pretty (keyDesc stk), "->", pretty (valueDesc stk)]
