module Concrete.Parse where

import Control.Applicative

import Bwd
import Concrete.Base
import Format
import Hide
import Parse
import Scope

instance Lisp Raw where
  mkNil = const (At "")
  mkCons = Cons
  pCar = ptm

pscoped :: Parser a -> Parser (Scope a)
pscoped p = Scope . Hide <$ pch (== '\\') <* pspc <*> pnom <* punc "." <*> p

pvariable :: Parser Variable
pvariable = Variable <$> pnom

ptm :: Parser Raw
ptm = Var <$> pvariable
  <|> At <$> patom
  <|> Lam <$> pscoped ptm
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* pch (== ')')
  <|> Sbst <$ pch (== '{') <* pspc <*> ppes (punc ",") psbstC <* punc "}" <*> ptm

psbstC :: Parser SbstC
psbstC = pvariable >>= \ x ->
  Assign x <$ punc "=" <*> ptm
  <|> Drop x <$ pspc <* pch (== '*')
  <|> pure (Keep x)

instance Lisp RawP where
  mkNil = const (AtP "")
  mkCons = ConsP
  pCar = ppat

ppat :: Parser RawP
ppat = VarP <$> pvariable
  <|> AtP <$> patom
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ppat <* pspc <* pch (== ')')
  <|> LamP <$> pscoped ppat
  <|> ThP <$ pch (== '{') <* pspc <*> pth <* punc "}" <*> ppat
  <|> UnderscoreP <$ pch (== '_')

pth :: Parser (Bwd Variable, ThDirective)
pth = (,) <$> ppes pspc pvariable
          <*> (ThDrop <$ pspc <* pch ('*' ==) <|> pure ThKeep)

pmode :: Parser Mode
pmode = Input <$ pch (== '?') <|> Output <$ pch (== '!')

pprotocol :: Parser (Protocol Raw)
pprotocol = psep pspc ((,) <$> pmode <* pspc <*> psyntaxdecl <* pspc <* pch (== '.'))

psyntaxdecl :: Parser Raw
psyntaxdecl = plocal B0 ptm

pjudgementstack :: Parser (JudgementStack Raw)
pjudgementstack =
   JudgementStack <$> psyntaxdecl <* punc "->" <*> psyntaxdecl <* punc "|-"

pACT :: Parser CActor
pACT = pact >>= more where

  more :: CActor -> Parser CActor
  more act = (act :|:) <$ punc "|" <*> pACT
    <|> pure act

withVar :: String -> Parser a -> Parser (Variable, a)
withVar str p = (,) <$> pvariable <* punc str <*> p

pextractmode :: Parser ExtractMode
pextractmode
    = TopLevelExtract <$ plit "/" <* pspc
  <|> InterestingExtract <$ plit "^" <* pspc
  <|> pure AlwaysExtract

pact :: Parser CActor
pact = Under <$> pscoped pact
  <|> Send <$> pvariable <* punc "!" <*> ptm <* punc "." <*> pact
  <|> questionmark <$> ptm <* punc "?" <*> withVar "." pact
  <|> Spawn <$> pextractmode <*> pvariable <* punc "@" <*> pvariable <* punc "." <*> pact
  <|> Constrain <$> ptm <* punc "~" <*> ptm
  <|> Connect <$> (CConnect <$> pvariable <* punc "<->" <*> pvariable)
  <|> Match <$ plit "case" <* pspc <*> ptm <* punc "{"
       <*> psep (punc ";") ((,) <$> ppat <* punc "->" <*> pACT)
       <* pspc <* pch (== '}')
  <|> id <$ pch (== '(') <* pspc <*> pACT <* pspc <* pch (== ')')
  <|> Break <$ plit "BREAK" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Print <$ plit "PRINT" <*> pargs [TermPart Instantiate ()] <* punc "." <*> pact
  <|> Print <$ plit "PRINTF" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Fail <$ pch (== '#') <* pspc <*> (pformat >>= pargs)
  <|> Push <$> pvariable <*> pcurlies (withVar "->" ptm) <* punc "." <*> pact
  <|> Lookup <$ plit "lookup" <* pspc <*> ptm <* pspc <*> pcurlies (withVar "->" pACT)
             <* pspc <* plit "else" <* pspc <*> pact
  <|> Note <$ plit "!" <* punc "." <*> pact
  <|> pure Win
  where
    questionmark (Var c) = Recv c
    questionmark t       = FreshMeta t

pargs :: [Format dir dbg ()] -> Parser [Format dir dbg Raw]
pargs = traverse $ traverse (\ () -> id <$ pspc <*> ptm)
