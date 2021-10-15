{-# LANGUAGE TupleSections, LambdaCase #-}

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

ptm :: Parser (CdB (Tm String))
ptm = var <$> join (pseek <$> pnom) <*> plen
  <|> atom <$ pch (== '\'') <*> pnom <*> plen
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    (x \\) <$> (pbind x ptm))
  <|> ($:) <$ pch (== '?') <*> pnom <*> (sbstI <$> plen)
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* pch (== ')')
  <|> id <$ pch (== '{') <* pspc <*> do
    (sg, xz) <- psbst
    pspc
    (//^ sg) <$> plocal xz ptm

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

plisp :: Parser (CdB (Tm String))
plisp = atom "" <$ pch (== ']') <*> plen
    <|> id <$ pch (== '|') <* pspc <*> ptm <* pspc <* pch (== ']')
    <|> (%) <$> ptm <* pspc <*> plisp

pnom :: Parser String
pnom = (:) <$> pch isAlpha <*> many (pch isMo) where
  isMo c = isAlphaNum c || elem c "_'"

pspc :: Parser ()
pspc = () <$ many (pch isSpace)

pnl :: Parser ()
pnl = () <$ pch (== '\n')

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

pseek :: String -> Parser Int
pseek x = Parser $ \ xz s -> let
  chug B0 = []
  chug (xz :< y)
    | y == x = [0]
    | otherwise = (1+) <$> chug xz
  in (, s) <$> chug xz

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

repl :: IO a
repl = forever $ getLine >>= \ s ->
         putStrLn (display' initNaming $ parse ptm s)
