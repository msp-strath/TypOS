module Term.Parse where

import Control.Applicative

import Hide
import Bwd
import Thin
import Term

import Parse

instance Lisp (CdB (Tm String)) where
  mkNil = atom ""
  mkCons = (%)
  pCar = ptm

ptm :: Parser (CdB (Tm String))
ptm = pvar (\ str -> (str $:) . sbstI <$> plen) (\ i -> var i <$> plen)
  <|> atom <$> patom <*> plen
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    (x \\) <$> (pbind x ptm))
  <|> glomQlist <$> plen <* pch (== '\'') <* pch (== '[') <* pspc <*> many (ptm <* pspc) <* pch (== ']')
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* pch (== ')')
  <|> id <$ pch (== '{') <* pspc <*> do
    (sg, xz) <- psbst
    pspc
    (//^ sg) <$> plocal xz ptm
  where
    glomQlist l = foldr qc qn where
      qc a d = ("Cons",l) #% [a, d]
      qn = ("Nil",l) #% []

psbst :: Parser (CdB (Sbst String), Bwd String)
psbst = (,) <$ pspc <* pch (== '}') <*> (sbstI <$> plen) <*> pscope
  <|> id <$ pch (== ',') <* pspc <*> psbst
  <|> (pnom >>= \ x -> pspc >> ppop x psbst >>= \ (sg, xz) ->
       pure (sbstW sg (ones 1), xz :< x))
  <|> (pnom >>= \ x -> pch (== '*') >> ppop x psbst >>= \ (sg, xz) ->
       pure (sbstW sg (none 1), xz))
  <|> do
    x <- pnom
    pspc ; pch (== '=') ; pspc
    (t, th) <- ptm
    (sg, xz) <- psbst
    return (sbstT sg ((Hide x := t), th), xz :< x)
