module Parse where

import Control.Applicative
import Control.Monad
import Data.Char

import Bwd

-- parsers, by convention, do not consume either leading
-- or trailing space

plit :: String -> Parser ()
plit = mapM_ (pch . (==))

punc :: String -> Parser ()
punc cs = () <$ pspc <* plit cs <* pspc

pstring :: Parser String
pstring = Parser $ \ xz str -> case str of
  '"' : str -> case span ('"' /=) str of
    (str, _:end) -> pure (str, end)
    _ -> []
  _ -> []

pnat :: Parser Int
pnat = Parser $ \ xz str -> case span isDigit str of
  (ds@(_:_), str) -> [(read ds, str)]
  _ -> []

pnom :: Parser String
pnom = Parser $
  let isMo c = isAlphaNum c || elem c "_'" in
  \ xz str -> case str of
  c : cs | isAlpha c -> case span isMo cs of
      (nm, str) -> [(c:nm, str)]
  _ -> []

pvar' :: Parser (String, Int)
pvar' = (,) <$> pnom <*> ((id <$ pch (== '^') <*> pnat) <|> pure 0)

pvar :: (String -> Parser a) -> (Int -> Parser a) -> Parser a
pvar str int = (either str int <=< pseek) =<< pvar'

patom :: Parser String
patom = pch (== '\'') *> pnom

pspc :: Parser ()
pspc = Parser $ \ xs str -> [((),snd (span isSpace str))]

pnl :: Parser ()
pnl = () <$ pch (\c -> c == '\n' || c == '\0')

psep :: Parser () -> Parser a -> Parser [a]
psep s p = (:) <$> p <*> many (id <$ s <*> p)
 <|> pure []

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

pseek :: (String, Int) -> Parser (Either String Int)
pseek (x, n) = Parser $ \ xz s -> let
  chug B0 n = [Left x]
  chug (xz :< y) n
    | y == x = if n == 0 then [Right 0] else fmap (1+) <$> chug xz (n - 1)
    | otherwise = fmap (1+) <$> chug xz n
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
  x -> error (show $ length x)

class Lisp t where
  mkNil  :: Int -> t
  mkCons :: t -> t -> t
  pCar   :: Parser t

plisp :: Lisp t => Parser t
plisp = mkNil <$ pch (== ']') <*> plen
    <|> id <$ pch (== '|') <* pspc <*> pCar <* pspc <* pch (== ']')
    <|> mkCons <$> pCar <* pspc <*> plisp
