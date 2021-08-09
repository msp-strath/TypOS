{-# LANGUAGE TupleSections #-}

module Parse where

import Control.Applicative
import Control.Monad
import Data.Char

import Bwd
import Thin
import Term

ptm :: Parser (Int -> CdB (Tm String))
ptm = var <$> join (pseek <$> pnom)
  <|> atom <$ pch (== '\'') <*> pnom
  <|> id <$ pch (== '\\') <* pspc <*> (do
    x <- pnom
    pspc
    pch (== '.')
    pspc
    (x \\) <$> pbind x ptm)
  <|> ($:) <$ pch (== '?') <*> pnom <*> pure
        (\ w -> ((S0, w), ones w))
  <|> id <$ pch (== '[') <* pspc <*> plisp
  <|> id <$ pch (== '(') <* pspc <*> ptm <* pspc <* pch (== ')')

plisp :: Parser (Int -> CdB (Tm String))
plisp = atom "" <$ pch (== ']')
    <|> id <$ pch (== '|') <* pspc <*> ptm <* pspc <* pch (== ']')
    <|> (%) <$> ptm <* pspc <*> plisp
  

pnom :: Parser String
pnom = (:) <$> pch isAlpha <*> many (pch isMo) where
  isMo c = isAlphaNum c || elem c "_'"

pspc :: Parser ()
pspc = () <$ many (pch isSpace)

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

plen :: Parser (Int -> x) -> Parser x
plen (Parser p) = Parser $ \ xz s -> do
  (f, s) <- p xz s
  return (f (length xz), s)