module Concrete.Parse where

import Control.Applicative

import Bwd
import Concrete.Base
import Format
import Hide
import Parse
import Scope
import Location

instance Lisp Raw where
  mkNil = At unknown ""
  mkCons = Cons unknown
  pCar = ptm

pscoped :: Parser x -> Parser a -> Parser (Scope x a)
pscoped px pa = Scope . Hide
  <$ pch (== '\\') <* pspc <*> pmustwork "Expected a binder" px
  <* punc "." <*> pa

pvariable :: Parser Variable
pvariable = withRange (Variable unknown <$> pnom)

pbinder :: Parser (Binder Variable)
pbinder = Used <$> pvariable
      <|> Unused <$ plit "_"

ptm :: Parser Raw
ptm = withRange $
  Var unknown <$> pvariable
  <|> At unknown <$> patom
  <|> Lam unknown <$> pscoped pbinder ptm
  <|> id <$ pch (== '[') <* pspc <*> pmustwork "Expected a list" plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* plit ")"
  <|> Sbst unknown <$ pch (== '{') <* pspc <*> ppes (punc ",") psbstC <* punc "}" <*> ptm

psbstC :: Parser SbstC
psbstC = withRange $ pvariable >>= \ x ->
  Assign unknown x <$ punc "=" <*> ptm
  <|> Drop unknown x <$ pspc <* pch (== '*')
  <|> pure (Keep unknown x)

instance Lisp RawP where
  mkNil = AtP unknown ""
  mkCons = ConsP unknown
  pCar = ppat

ppat :: Parser RawP
ppat = withRange $
  VarP unknown <$> pvariable
  <|> AtP unknown <$> patom
  <|> id <$ pch (== '[') <* pspc <*> pmustwork "Expected a list pattern" plisp
  <|> id <$ pch (== '(') <* pspc <*> ppat <* pspc <* pmustwork "Expected a closing parens" (plit ")")
  <|> LamP unknown <$> pscoped pbinder ppat
  <|> ThP unknown <$ pch (== '{') <* pspc <*> pth <* punc "}" <*> ppat
  <|> UnderscoreP unknown <$ pch (== '_')

pth :: Parser (Bwd Variable, ThDirective)
pth = (,) <$> ppes pspc pvariable
          <*> (ThDrop <$ pspc <* pch ('*' ==) <|> pure ThKeep)

pmode :: Parser Mode
pmode = Input <$ pch (== '?') <|> Output <$ pch (== '!')

pprotocol :: Parser (Protocol Raw)
pprotocol = psep pspc
  ((,) <$> pmode <* pspc
       <*> pmustwork "Expected a syntax declaration" psyntaxdecl
       <* pspc <* plit ".")

psyntaxdecl :: Parser Raw
psyntaxdecl = ptm

pjudgementstack :: Parser (JudgementStack Raw)
pjudgementstack = JudgementStack
  <$> psyntaxdecl
  <* punc "->"
  <*> pmustwork "Expected a syntax declaration" psyntaxdecl
  <* pmustwork "Expected \"|-\"" (punc "|-")

pACT :: Parser CActor
pACT = withRange (pact >>= more) where

  more :: CActor -> Parser CActor
  more act = Branch unknown act <$ punc "|" <*> pmustwork "Expected an actor" pACT
    <|> pure act

withVar :: Parser x -> String -> Parser a -> Parser (x, a)
withVar px str p = (,) <$> px <* punc str <*> p

pextractmode :: Parser ExtractMode
pextractmode
    = TopLevelExtract <$ pch (== '/') <* pspc
  <|> InterestingExtract <$ pch (== '^') <* pspc
  <|> pure AlwaysExtract

pact :: Parser CActor
pact = withRange $
  Under unknown <$> pscoped pvariable pact
  <|> Send unknown <$> pvariable <* punc "!" <*> pmustwork "Expected a term" ptm <* punc "." <*> pact
  <|> do tm <- ptm
         punc "?"
         case tm of
           Var _ c -> Recv unknown c <$> withVar pbinder "." pact
           t -> FreshMeta unknown t <$> withVar pvariable "." pact
  <|> Spawn unknown <$> pextractmode <*> pvariable <* punc "@" <*> pvariable <* punc "." <*> pact
  <|> Constrain unknown <$> ptm <* punc "~" <*> pmustwork "Expected a term" ptm
  <|> Connect unknown <$> (CConnect <$> pvariable <* punc "<->" <*> pvariable)
  <|> Match unknown <$ plit "case" <* pspc <*> ptm <* punc "{"
       <*> psep (punc ";") ((,) <$> ppat <* punc "->" <*> pACT)
       <* pspc <* pch (== '}')
  <|> id <$ pch (== '(') <* pspc <*> pACT <* pspc <* plit ")"
  <|> Break unknown <$ plit "BREAK" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Print unknown <$ plit "PRINT" <*> pargs [TermPart Instantiate ()] <* punc "." <*> pact
  <|> Print unknown <$ plit "PRINTF" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Fail unknown <$ pch (== '#') <* pspc <*> (pformat >>= pargs)
  <|> Push unknown <$> pvariable <*> pcurlies ((\ (a, b) -> (a, (), b)) <$> withVar pvariable "->" ptm) <* punc "." <*> pact
  <|> Lookup unknown <$ plit "lookup" <* pspc <*> ptm <* pspc <*> pcurlies (withVar pbinder "->" pACT)
             <* pspc <* pmustwork "Expected an else branch" (plit "else") <* pspc <*> pact
  <|> Note unknown <$ plit "!" <* punc "." <*> pact
  <|> pure (Win unknown)

pargs :: [Format dir dbg ()] -> Parser [Format dir dbg Raw]
pargs = traverse $ traverse (\ () -> id <$ pspc <*> pmustwork "Expected a term" ptm)
