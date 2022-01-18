module Parse where

import Control.Applicative
import Control.Monad
import Data.Char

import Hide
import Bwd
import Thin
import Term

-- parsers, by convention, do not consume either leading
-- or trailing space

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

pnat :: Parser Int
pnat = Parser $ \ xz str -> case span isDigit str of
  (ds@(_:_), str) -> [(read ds, str)]
  _ -> []

pvar' :: Parser (String, Int)
pvar' = (,) <$> pnom <*> ((id <$ pch (== '^') <*> pnat) <|> pure 0)

pvar :: Parser Int
pvar = pseek =<< pvar'

ppat :: Parser Pat
ppat = VP <$> pvar
  <|> AP <$ pch (== '\'') <*> pnom
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ppat <* pspc <* pch (== ')')
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    (BP (Hide x)) <$> (pbind x ppat))
  <|> MP <$ pch (== '?') <*> pnom <*> (ones <$> plen)
  <|> id <$ pch (== '{') <* pspc <*> do
    (th, xz) <- pth
    pspc
    (*^ th) <$> plocal xz ppat

ptm :: Parser (CdB (Tm String))
ptm = var <$> pvar <*> plen
  <|> atom <$ pch (== '\'') <*> pnom <*> plen
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    (x \\) <$> (pbind x ptm))
  <|> ($:) <$ pch (== '?') <*> pnom <*> (sbstI <$> plen)
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

pnom :: Parser String
pnom = (:) <$> pch isAlpha <*> many (pch isMo) where
  isMo c = isAlphaNum c || elem c "_'"

pspc :: Parser ()
pspc = () <$ many (pch isSpace)

pnl :: Parser ()
pnl = () <$ pch (\c -> c == '\n' || c == '\0')

data Parser a = Parser
  { parser :: Bwd String -> String -> [(a, String)]
  }

instance Monad Parser where
  return a = Parser $ \ xz s -> [(a, s)]
  Parser f >>= k = Parser $ \ xz s -> do
    (a, s) <- f xz s
    parser (k a) xz s

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Functor Parser where
  fmap = ap . return

instance Alternative Parser where
  empty = Parser $ \ _ _ -> []
  Parser f <|> Parser g = Parser $ \ xz s ->
    f xz s ++ g xz s

pbind :: String -> Parser a -> Parser a
pbind x (Parser p) = Parser $ \ xz s -> p (xz :< x) s

pscope :: Parser (Bwd String)
pscope = Parser $ \ xz s -> [(xz, s)]

plen :: Parser Int
plen = length <$> pscope

plocal :: Bwd String -> Parser x -> Parser x
plocal xz (Parser p) = Parser $ \ _ s -> p xz s

ppop :: String -> Parser x -> Parser x
ppop x p = pscope >>= \case
  xz :< y | x == y -> plocal xz p
  _ -> empty

pseek :: (String, Int) -> Parser Int
pseek (x, n) = Parser $ \ xz s -> let
  chug B0 n = []
  chug (xz :< y) n
    | y == x = if n == 0 then [0] else (1+) <$> chug xz (n - 1)
    | otherwise = (1+) <$> chug xz n
  in (, s) <$> chug xz n

pch :: (Char -> Bool) -> Parser Char
pch p = Parser $ \ xz s -> case s of
  c : cs | p c -> [(c, cs)]
  _ -> []

pend :: Parser ()
pend = Parser $ \ xz s -> case s of
  [] -> [((), "")]
  _ -> []

parse :: Parser x -> String -> x
parse p s = case parser (id <$> p <* pend) B0 s of
  [(x, _)] -> x
