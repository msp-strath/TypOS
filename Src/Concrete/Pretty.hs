{-# LANGUAGE OverloadedStrings #-}

module Concrete.Pretty where

import Data.Foldable

import Bwd
import Concrete.Base
import Format
import Hide
import Scope
import Pretty

instance Pretty x => Pretty (Hide x) where
  pretty (Hide x) = pretty x

instance Pretty Variable where
  pretty (Variable _ v) = pretty v

instance Pretty x => Pretty (Binder x) where
  pretty (Used v) = pretty v
  pretty (Unused _) = "_"

multiBind :: Bwd (Hide (Binder Variable)) -> Raw -> Doc Annotations
multiBind xs (Lam _ (Scope x t)) = multiBind (xs :< x) t
multiBind xs t = backslash <> hsep (pretty <$> xs <>> []) <> dot <+> pretty t

instance Pretty Raw where
  prettyPrec d = \case
    Var _ v -> pretty v
    At _ [] -> "[]"
    At _ at -> squote <> pretty at
    Cons _ p q -> brackets $ case pretty p : prettyCdr q of
      (d : ds@(_:_)) -> d </> sep ds
      ds -> hsep ds
    Lam _ (Scope x t) -> parenthesise (d > 0) $ multiBind (B0 :< x) t
    Sbst _ B0 t -> prettyPrec d t
    Sbst _ sg t -> parenthesise (d > 0) $ hsep [ pretty sg, pretty t ]
    Op _ s t -> parenthesise (d > 0) $ hsep [ pretty s, "-", prettyPrec 1 t ]
    Rad _ s t -> parenthesise (d > 0) $ hsep [ pretty s, ":", pretty t ]
    Guarded g t -> hsep [ "<", pretty t , ">"]
    Thicken _ (thxz, thd) t -> braces (hsep (pretty <$> thxz <>> []) <> pretty thd) <+> pretty t

instance Pretty (Bwd Assign) where
  pretty sg = encloseSep lbrace rbrace ", " $ pretty <$> sg <>> []

prettyCdr :: Raw -> [Doc Annotations]
prettyCdr = \case
  At _ [] -> []
  Cons _ p q -> pretty p : prettyCdr q
  p -> [pipe, pretty p]

instance Pretty Assign where
  pretty = \case
    Assign _ x t -> pretty x <> equals <> pretty t

instance Pretty ThDirective where
  pretty = \case
    ThKeep -> ""
    ThDrop -> "*"

multiBindP :: Bwd (Hide (Binder Variable)) -> RawP -> Doc Annotations
multiBindP xs (LamP _ (Scope x t)) = multiBindP (xs :< x) t
multiBindP xs t = backslash <> hsep (pretty <$> xs <>> []) <> dot <+> pretty t

instance Pretty RawP where
  prettyPrec d = \case
    AsP _ v p -> pretty v <> "@" <> pretty p
    VarP _ v -> pretty v
    AtP _ "" -> "[]"
    AtP _ at -> squote <> pretty at
    ConsP _ p q -> brackets $ sep (pretty p : prettyCdrP q)
    LamP _ (Scope x p) -> multiBindP (B0 :< x) p
    ThP _ (thxz, thd) p -> braces (hsep (pretty <$> thxz <>> []) <> pretty thd) <+> pretty p
    UnderscoreP _ -> "_"

prettyCdrP :: RawP -> [Doc Annotations]
prettyCdrP = \case
  AtP _ [] -> []
  ConsP _ p q -> pretty p : prettyCdrP q
  p -> [pipe, pretty p]

instance Pretty CScrutinee where
  prettyPrec d = \case
    SubjectVar _ t -> prettyPrec d t
    Term _ t -> prettyPrec d t
    Pair _ s t -> brackets $ sep (pretty s : prettyCdrS t)
    Lookup _ stk t -> hsep ["lookup", pretty stk, pretty t]
    Compare _ s t -> hsep ["compare", pretty s, pretty t]

prettyCdrS :: CScrutinee -> [Doc Annotations]
prettyCdrS = \case
  Term _ (At _ "") -> []
  Pair _ p q -> pretty p : prettyCdrS q
  p -> [pipe, pretty p]

instance Pretty ExtractMode where
  pretty = \case
    AlwaysExtract -> ""
    TopLevelExtract -> "/"
    InterestingExtract -> "^"

-- Just like we have a distinction between small and big actors in the parser,
-- it makes sense to have one in the pretty printer too.
prettyact :: CActor -> [Doc Annotations]
prettyact = go B0 B0 where

  add :: Bwd (Doc Annotations) -> [Doc Annotations] -> Bwd (Doc Annotations)
  add B0 ds = B0 <>< ds
  add sd ds = sd <>< (space : ds)

  go :: Bwd (Doc Annotations) -> -- lines above us
        Bwd (Doc Annotations) -> -- part of the line on our left
        CActor -> [Doc Annotations]
  go ls l = \case
    Spawn r em jd p a -> go (ls :< fold (l `add` [pretty em, pretty jd, "@", pretty p, dot])) B0 a
    Send r ch _ t@(Var _ _) a -> go ls (l `add` [pretty ch, "!", pretty t, dot]) a
    Send r ch _ t a -> go (ls :< fold (l `add` [pretty ch, "!", pretty t, dot])) B0 a
    Recv r ch (av, a) -> go ls (l `add` [pretty ch, "?", pretty av, dot]) a
    FreshMeta r syn (av, a) -> freshMetas ls l syn (B0 :< av) a
    Let r av syn t a -> go (ls :< fold (l `add` [hsep ["let", pretty av, ":", pretty syn, "=", pretty t] <> dot])) B0 a
    Under r mty (Scope x a) -> unders ls l mty (B0 :< x) a
    Note r a -> go ls (l `add` ["!", dot]) a
    Push r stk (x, _, t) a ->
      let push = hsep [pretty stk, "|-", pretty x, "->", pretty t] <> dot in
      go (ls :< fold (l `add` [push])) B0 a
    Print r [TermPart Instantiate tm] a -> go (ls :< fold (l `add` [hsep [keyword "PRINT", pretty tm] <> dot])) B0 a
    Print r fmt a -> go (ls :< fold (l `add` [hsep [keyword "PRINTF", pretty fmt] <> dot])) B0 a
    Break r fmt a -> go (ls :< fold (l `add` [hsep [keyword "BREAK", pretty fmt] <> dot])) B0 a
    -- if we win, avoid generating an empty line
    Win r -> case l of
             B0 -> ls <>> []
             _ -> ls <>> [fold l]
    a -> ls <>> [fold (l `add` [prettyPrec 1 a])] -- either a big one or a final one

  freshMetas :: Bwd (Doc Annotations) -> -- lines above us
                Bwd (Doc Annotations) -> -- part of the line on our left
                Raw -> Bwd Variable -> CActor -> [Doc Annotations]
  freshMetas ls l syn avs (FreshMeta _ syn' (av, a)) | syn == syn' = freshMetas ls l syn (avs :< av) a
  freshMetas ls l syn avs a = go (ls :< fold (l `add` [pretty syn, "?", hsep (pretty <$> avs <>> []), dot])) B0 a

  unders :: Bwd (Doc Annotations) -> -- lines above us
            Bwd (Doc Annotations) -> -- part of the line on our left
            Maybe Raw -> -- Type annotation
            Bwd (Hide Variable) -> CActor -> [Doc Annotations]
  unders ls l mty xs (Under _ mty' (Scope x a))
       | mty == mty' = unders ls l mty (xs :< x) a
  unders ls l mty xs a
    = go ls (l `add` [ maybe id (\ ty r -> pretty ty <+> r) mty backslash
                     , hsep (pretty <$> xs <>> [])
                     , dot]) a


instance Pretty CActor where
  prettyPrec d = \case
    -- big ones
    Branch r a b -> parenthesise (d > 0) $ sep [ prettyPrec 1 a, pipe <+> pretty b ]
    Match r tm pts ->
      let match = hsep [ keyword "case", pretty tm ]
          cls   = map pretty pts
      in
      hang 2 match $ encloseSep "{ " "}" "; " cls
    Connect r cnnct -> pretty cnnct
    -- final actors
    Win r -> ""
    Fail r fmt -> "#" <> pretty fmt
    Constrain r s t -> hsep [ pretty s, "~", pretty t ]
    -- right nested small actors
    a -> sep (prettyact a)

instance Pretty Debug where
  pretty = \case
    ShowEnv -> "%E"
    ShowStack -> "%S"
    ShowStore -> "%M"

instance Pretty Directive where
  pretty = \case
    Raw -> "%r"
    Instantiate -> "%i"
    ShowT -> "%s"
    Normalise -> "%n"

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
     hang 2 (hsep [pp, "->"]) pa

instance Pretty (Mode a) where
  pretty Input   = "?"
  pretty (Subject _) = "$"
  pretty Output  = "!"

instance Pretty t => Pretty (Mode a, t) where
  pretty (m, desc) = hsep [ pretty m, prettyPrec 1 desc ]

instance Pretty CProtocol where
  pretty (Protocol ps) = foldMap (\ x -> pretty x <> ". ") ps

instance (Pretty k, Pretty v) => Pretty (ContextStack k v) where
  pretty stk = hsep [pretty (keyDesc stk), "->", pretty (valueDesc stk)]

instance Pretty CConnect where
  pretty (CConnect ch1 ch2) = hsep [pretty ch1, "<->", pretty ch2]
