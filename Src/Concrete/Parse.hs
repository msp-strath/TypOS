module Concrete.Parse where

import Control.Applicative

import Bwd
import Concrete.Base
import Format
import Hide
import Parse
import Scope

instance Lisp Raw where
  mkNil = At ""
  mkCons = Cons
  pCar = ptm

pscoped :: Parser x -> Parser a -> Parser (Scope x a)
pscoped px pa = Scope . Hide
  <$ pch (== '\\') <* pspc <*> pmustwork "Expected a binder" px
  <* punc "." <*> pa

pvariable :: Parser Variable
pvariable = Variable <$> pnom

pbinder :: Parser (Binder Variable)
pbinder = Used <$> pvariable
      <|> Unused <$ plit "_"

ptm :: Parser Raw
ptm = Var <$> pvariable
  <|> At <$> patom
  <|> Lam <$> pscoped pbinder ptm
  <|> id <$ pch (== '[') <* pspc <*> pmustwork "Expected a list" plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* pch (== ')')
  <|> Sbst <$ pch (== '{') <* pspc <*> ppes (punc ",") psbstC <* punc "}" <*> ptm

psbstC :: Parser SbstC
psbstC = pvariable >>= \ x ->
  Assign x <$ punc "=" <*> ptm
  <|> Drop x <$ pspc <* pch (== '*')
  <|> pure (Keep x)

instance Lisp RawP where
  mkNil = AtP ""
  mkCons = ConsP
  pCar = ppat

ppat :: Parser RawP
ppat = VarP <$> pvariable
  <|> AtP <$> patom
  <|> id <$ pch (== '[') <* pspc <*> pmustwork "Expected a list pattern" plisp
  <|> id <$ pch (== '(') <* pspc <*> ppat <* pspc <* pmustwork "Expected a closing parens" (pch (== ')'))
  <|> LamP <$> pscoped pbinder ppat
  <|> ThP <$ pch (== '{') <* pspc <*> pth <* punc "}" <*> ppat
  <|> UnderscoreP <$ pch (== '_')

pth :: Parser (Bwd Variable, ThDirective)
pth = (,) <$> ppes pspc pvariable
          <*> (ThDrop <$ pspc <* pch ('*' ==) <|> pure ThKeep)

pmode :: Parser Mode
pmode = Input <$ pch (== '?') <|> Output <$ pch (== '!')

pprotocol :: Parser (Protocol Raw)
pprotocol = psep pspc
  ((,) <$> pmode <* pspc
       <*> pmustwork "Expected a syntax declaration" psyntaxdecl
       <* pspc <* pch (== '.'))

psyntaxdecl :: Parser Raw
psyntaxdecl = ptm

pjudgementstack :: Parser (JudgementStack Raw)
pjudgementstack = JudgementStack
  <$> psyntaxdecl
  <* punc "->"
  <*> pmustwork "Expected a syntax declaration" psyntaxdecl
  <* pmustwork "Expected \"|-\"" (punc "|-")

pACT :: Parser CActor
pACT = pact >>= more where

  more :: CActor -> Parser CActor
  more act = (act :|:) <$ punc "|" <*> pmustwork "Expected an actor" pACT
    <|> pure act

withVar :: Parser x -> String -> Parser a -> Parser (x, a)
withVar px str p = (,) <$> px <* punc str <*> p

pextractmode :: Parser ExtractMode
pextractmode
    = TopLevelExtract <$ plit "/" <* pspc
  <|> InterestingExtract <$ plit "^" <* pspc
  <|> pure AlwaysExtract

pact :: Parser CActor
pact = Under <$> pscoped pnom pact
  <|> Send <$> pvariable <* punc "!" <*> pmustwork "Expected a term" ptm <* punc "." <*> pact
  <|> do tm <- ptm
         punc "?"
         case tm of
           Var c -> Recv c <$> withVar pbinder "." pact
           t -> FreshMeta t <$> withVar pvariable "." pact
  <|> Spawn <$> pextractmode <*> pvariable <* punc "@" <*> pvariable <* punc "." <*> pact
  <|> Constrain <$> ptm <* punc "~" <*> pmustwork "Expected a term" ptm
  <|> Connect <$> (CConnect <$> pvariable <* punc "<->" <*> pvariable)
  <|> Match <$ plit "case" <* pspc <*> ptm <* punc "{"
       <*> psep (punc ";") ((,) <$> ppat <* punc "->" <*> pACT)
       <* pspc <* pch (== '}')
  <|> id <$ pch (== '(') <* pspc <*> pACT <* pspc <* pch (== ')')
  <|> Break <$ plit "BREAK" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Print <$ plit "PRINT" <*> pargs [TermPart Instantiate ()] <* punc "." <*> pact
  <|> Print <$ plit "PRINTF" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Fail <$ pch (== '#') <* pspc <*> (pformat >>= pargs)
  <|> Push <$> pvariable <*> pcurlies ((\ (a, b) -> (a, (), b)) <$> withVar pvariable "->" ptm) <* punc "." <*> pact
  <|> Lookup <$ plit "lookup" <* pspc <*> ptm <* pspc <*> pcurlies (withVar pbinder "->" pACT)
             <* pspc <* pmustwork "Expected an else branch" (plit "else") <* pspc <*> pact
  <|> Note <$ plit "!" <* punc "." <*> pact
  <|> pure Win
  where
    questionmark (Var c) = Recv c
    questionmark t       = FreshMeta t

pargs :: [Format dir dbg ()] -> Parser [Format dir dbg Raw]
pargs = traverse $ traverse (\ () -> id <$ pspc <*> pmustwork "Expected a term" ptm)
