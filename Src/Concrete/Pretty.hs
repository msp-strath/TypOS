module Concrete.Pretty where

import Data.List

import Bwd
import Concrete.Base
import Format
import Hide
import Scope
import Pretty

instance Pretty (Hide String) where
  pretty (Hide x) = x

instance Pretty Variable where
  pretty (Variable v) = v

instance Pretty Raw where
  pretty = \case
    Var v -> pretty v
    At [] -> "[]"
    At at -> '\'' : at
    Cons p q -> brackets $ pretty p ++ prettyCdr q
    Lam (Scope x t) -> '\\' : pretty x ++ '.' : pretty t
    Sbst B0 t -> pretty t
    Sbst sg t -> unwords [ pretty sg, pretty t ]

instance Pretty (Bwd SbstC) where
  pretty sg = braces (intercalate "," $ pretty <$> sg <>> [])

prettyCdr :: Raw -> String
prettyCdr = \case
  At [] -> ""
  Cons p q -> ' ' : pretty p ++ prettyCdr q
  p -> '|' : pretty p

instance Pretty SbstC where
  pretty = \case
    Keep x -> pretty x
    Drop x -> pretty x ++ "*"
    Assign x t -> pretty x ++ '=' : pretty t

instance Pretty ThDirective where
  pretty = \case
    ThKeep -> ""
    ThDrop -> "*"

instance Pretty RawP where
  prettyPrec d = \case
    VarP v -> pretty v
    AtP at -> '\'' : at
    ConsP p q -> brackets $ pretty p ++ prettyCdrP q
    LamP (Scope x p) -> '\\' : pretty x ++ '.' : pretty p
    ThP (thxz, thd) p -> braces (intercalate " " (pretty <$> thxz <>> []) ++ pretty thd) ++ pretty p
    UnderscoreP -> "_"

prettyCdrP :: RawP -> String
prettyCdrP = \case
  AtP [] -> ""
  ConsP p q -> ' ' : pretty p ++ prettyCdrP q
  p -> '|' : pretty p

instance Pretty Actor where
  prettyPrec d = \case
    a :|: b -> parenthesise (d > 0) $ unwords [ prettyPrec 1 a, "|", pretty b ]
    Spawn jd p a -> concat [ pretty jd, "@", pretty p, ". ", prettyPrec 1 a ]
    Send ch t a -> concat [ pretty ch, "!", pretty t, ". ", prettyPrec 1 a ]
    Recv ch (av, a) -> concat [ pretty ch, "?", pretty av, ". ", prettyPrec 1 a ]
    FreshMeta syn (av, a) -> concat [ pretty syn, "?", pretty av, ". ", prettyPrec 1 a ]
    Under (Scope x a) -> concat [ "\\", pretty x, ". ", prettyPrec 1 a ]
    Match tm pts -> unwords [ "case", pretty tm, "of", braces (intercalate ";" $ map pretty pts) ]
    Constrain s t -> unwords [ pretty s, "~", pretty t ]
    Push jd (x, t) a -> unwords [ pretty jd, braces (unwords [ pretty x, "->", pretty t ]) ++ ".", prettyPrec 1 a]
    Lookup tm (av, a) b -> unwords [ "lookup", pretty tm, braces (unwords [ pretty av, "->", pretty a ])
                                   , "else", prettyPrec 1 a ]
    Win -> ""
    Fail fmt -> '#' : pretty fmt
    Print [TermPart Instantiate tm] a -> unwords ["PRINT", pretty tm, ".", prettyPrec 1 a]
    Print fmt a -> unwords ["PRINTF", pretty fmt, ".", prettyPrec 1 a]
    Break fmt a -> unwords ["BREAK", pretty fmt, ".", prettyPrec 1 a]

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

    go fmt args [] = unwords (('"' : concat fmt ++ ['"']) : args <>> [])
    go fmt args (f:fs) = case f of
      TermPart d t -> go (fmt :< pretty d) (args :< pretty t) fs
      DebugPart dbg -> go (fmt :< pretty dbg) args fs
      StringPart str -> go (fmt :< escape str) args fs

instance Pretty (RawP, Actor) where
  pretty (p, a) = unwords [ pretty p, "->", pretty a ]
