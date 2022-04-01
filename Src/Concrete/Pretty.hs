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

-- Just like we have a distinction between small and big actors in the parser,
-- it makes sense to have one in the pretty printer too.
prettyact :: CActor -> [Doc Annotations]
prettyact a = go B0 B0 a where

  add :: Bwd (Doc Annotations) -> [Doc Annotations] -> Bwd (Doc Annotations)
  add B0 ds = B0 <>< ds
  add sd ds = sd <>< (space : ds)

  go :: Bwd (Doc Annotations) -> -- lines above us
        Bwd (Doc Annotations) -> -- part of the line on our left
        CActor -> [Doc Annotations]
  go ls l = \case
    Spawn jd p a -> go (ls :< fold (l `add` [pretty jd, "@", pretty p, dot])) B0 a
    Send ch t@(Var _) a -> go ls (l `add` [pretty ch, "!", pretty t, dot]) a
    Send ch t a -> go (ls :< fold (l `add` [pretty ch, "!", pretty t, dot])) B0 a
    Recv ch (av, a) -> go ls (l `add` [pretty ch, "?", pretty av, dot]) a
    FreshMeta syn (av, a) -> go (ls :< fold (l `add` [pretty syn, "?", pretty av, dot])) B0 a
    Under (Scope x a) -> go ls (l `add` [backslash , pretty x, dot]) a
    Push jd (x, t) a ->
      let push = hsep [pretty jd, braces (hsep [ pretty x, "->", pretty t])] <> dot in
      go (ls :< (fold (l `add` [push]))) B0 a
    Print [TermPart Instantiate tm] a -> go (ls :< (fold (l `add` [hsep [keyword "PRINT", pretty tm] <> dot]))) B0 a
    Print fmt a -> go (ls :< (fold (l `add` [hsep [keyword "PRINTF", pretty fmt] <> dot]))) B0 a
    Break fmt a -> go (ls :< (fold (l `add` [hsep [keyword "BREAK", pretty fmt] <> dot]))) B0 a
    -- if we win, avoid generating an empty line
    Win -> case l of
             B0 -> ls <>> []
             _ -> ls <>> [fold l]
    a -> ls <>> [fold (l `add` [prettyPrec 1 a])] -- either a big one or a final one

instance Pretty CActor where
  prettyPrec d = \case
    -- big ones
    a :|: b -> parenthesise (d > 0) $ sep [ prettyPrec 1 a, pipe <+> pretty b ]
    Match tm pts ->
      let match = hsep [ keyword "case", pretty tm ]
          cls   = map pretty pts
      in alts
      [ fold [ flush match
             , flush (indent 2 $ vcat $ zipWith (<+>) ("{": repeat ";") cls)
             , indent 2 "}"
             ]
      , hsep [ match , braces (sep $ intersperse ";" cls) ]
      ]
    Lookup tm (av, a) b -> sep
      [ hsep [ keyword "lookup", pretty tm, braces (hsep [ pretty av, "->", pretty a ]), keyword "else" ]
      , prettyPrec 1 a ]
    Connect cnnct -> pretty cnnct
    -- final actors
    Win -> ""
    Fail fmt -> "#" <> pretty fmt
    Constrain s t -> hsep [ pretty s, "~", pretty t ]
    -- right nested small actors
    a -> sep (prettyact a)

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

instance Pretty (RawP, CActor) where
  pretty (p, a) =
     let pp = pretty p; pa = sep (prettyact a) in
     alts [ hsep [pp, "->", pa ]
          , hsep [pp, "->"] $$ indent 2 pa ]

instance Pretty Mode where
  pretty Input = "?"
  pretty Output = "!"

instance Pretty t => Pretty (Protocol t) where
  pretty = foldMap $ \ (m, d) -> fold [pretty m, pretty d, ". "]

instance Pretty t => Pretty (JudgementStack t) where
  pretty stk = hsep [pretty (keyDesc stk), "->", pretty (valueDesc stk)]

instance Pretty CConnect where
  pretty (CConnect ch1 ch2) = hsep [pretty ch1, "<->", pretty ch2]
