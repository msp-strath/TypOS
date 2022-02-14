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
ptm = pvar ptmmeta (\ i -> var i <$> plen)
  <|> atom <$> patom <*> plen
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    punc "."
    (x \\) <$> (pbind x ptm))
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* pch (== ')')
  <|> id <$ pch (== '{') <* pspc <*> do
    (sg, xz) <- psbst
    pspc
    (//^ sg) <$> plocal xz ptm
  where
    ptmmeta str = do
      xz <- pmeta str
      sc <- pscope
      case findSub xz sc of
        Just th -> pure (str $: sbstW (sbst0 0) th)
        Nothing -> empty

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
