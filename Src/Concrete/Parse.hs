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

ptm :: Parser Raw
ptm = Var <$> pnom
  <|> At <$> patom
  <|> Lam <$> pscoped ptm
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* pch (== ')')
  <|> Sbst <$ pch (== '{') <* pspc <*> ppes (punc ",") psbstC <* punc "}" <*> ptm

psbstC :: Parser SbstC
psbstC = pnom >>= \ x ->
  Assign x <$ punc "=" <*> ptm
  <|> Drop x <$ pspc <* pch (== '*')
  <|> pure (Keep x)

instance Lisp RawP where
  mkNil = const (AtP "")
  mkCons = ConsP
  pCar = ppat

ppat :: Parser RawP
ppat = VarP <$> pnom
  <|> AtP <$> patom
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ppat <* pspc <* pch (== ')')
  <|> LamP <$> pscoped ppat
  <|> ThP <$ pch (== '{') <* pspc <*> pth <* punc "}" <*> ppat
  <|> UnderscoreP <$ pch (== '_')

pth :: Parser (Bwd Variable, ThDirective)
pth = (,) <$> ppes pspc pnom
          <*> (ThDrop <$ pspc <* pch ('*' ==) <|> pure ThKeep)

pACT :: Parser Actor
pACT = pact >>= more where

  more :: Actor -> Parser Actor
  more act = (act :|:) <$ punc "|" <*> pACT
    <|> pure act

withVar :: String -> Parser a -> Parser (Variable, a)
withVar str p = (,) <$> pnom <* punc str <*> p

pact :: Parser Actor
pact = Under <$> pscoped pact
  <|> Send <$> pnom <* punc "!" <*> ptm <* punc "." <*> pact
  <|> Recv <$> pnom <* punc "?" <*> withVar "." pact
  <|> FreshMeta <$ pch (== '?') <* pspc <*> withVar "." pact
  <|> Spawn <$> pnom <* punc "@" <*> pnom <* punc "." <*> pact
  <|> Constrain <$> ptm <* punc "~" <*> ptm
  <|> Match <$ plit "case" <* pspc <*> ptm <* punc "{"
       <*> psep (punc ";") ((,) <$> ppat <* punc "->" <*> pACT)
       <* pspc <* pch (== '}')
  <|> id <$ pch (== '(') <* pspc <*> pACT <* pspc <* pch (== ')')
  <|> Break <$ plit "BREAK" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Print <$ plit "PRINT" <*> pargs [TermPart Instantiate ()] <* punc "." <*> pact
  <|> Print <$ plit "PRINTF" <* pspc <*> (pformat >>= pargs) <* punc "." <*> pact
  <|> Fail <$ pch (== '#') <* pspc <*> (pformat >>= pargs)
  <|> Push <$> pnom <*> pcurlies (withVar "->" ptm) <* punc "." <*> pact
  <|> Lookup <$ plit "lookup" <* pspc <*> ptm <* pspc <*> pcurlies (withVar "->" pACT)
             <* pspc <* plit "else" <* pspc <*> pact
  <|> pure Win

pargs :: [Format dir dbg ()] -> Parser [Format dir dbg Raw]
pargs = traverse $ traverse (\ () -> id <$ pspc <*> ptm)
