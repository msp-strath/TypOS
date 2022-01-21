module Term.Parse where

import Control.Applicative
import Control.Monad

import Hide
import Bwd
import Thin
import Term

import Parse

class Lisp t where
  mkNil  :: Int -> t
  mkCons :: t -> t -> t
  pCar   :: Parser t

instance Lisp (CdB (Tm String)) where
  mkNil = atom ""
  mkCons = (%)
  pCar = ptm

instance Lisp Pat where
  mkNil = const (AP "")
  mkCons = PP
  pCar = ppat

pvar' :: Parser (String, Int)
pvar' = (,) <$> pnom <*> ((id <$ pch (== '^') <*> pnat) <|> pure 0)

pvar :: (String -> Parser a) -> (Int -> Parser a) -> Parser a
pvar str int = (either str int <=< pseek) =<< pvar'

patom :: Parser String
patom = pch (== '\'') *> pnom

ppat :: Parser Pat
ppat = pvar (\ str -> MP str . ones <$> plen) (pure . VP)
  <|> AP <$> patom
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ppat <* pspc <* pch (== ')')
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    (BP (Hide x)) <$> (pbind x ppat))
  <|> id <$ pch (== '{') <* pspc <*> do
    (th, xz) <- pth
    pspc
    (*^ th) <$> plocal xz ppat

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

pth :: Parser (Th, Bwd String)
pth = do
  (xns, b) <- raw
  xz <- pscope
  let xnz = deBruijnify xz
  let th = (if b then comp else id) (which (`elem` xns) xnz)
  pure (th, th ^? xz)

  where

  raw :: Parser ([(String, Int)], Bool)
  raw = (,) <$> many (id <$ pspc <*> pvar') <* pspc
            <*> (True <$ pch (== '*') <|> pure False)
            <* pspc <* pch (== '}')

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

plisp :: Lisp t => Parser t
plisp = mkNil <$ pch (== ']') <*> plen
    <|> id <$ pch (== '|') <* pspc <*> pCar <* pspc <* pch (== ']')
    <|> mkCons <$> pCar <* pspc <*> plisp
