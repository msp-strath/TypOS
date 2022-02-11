module Parse where

import Control.Applicative
import Control.Monad
import Data.Char

import Data.Map (Map)
import qualified Data.Map as Map

import Bwd

-- parsers, by convention, do not consume either leading
-- or trailing space

poptional :: Parser a -> Parser (Maybe a)
poptional p = Just <$> p <|> pure Nothing

plit :: String -> Parser ()
plit = mapM_ (pch . (==))

punc :: String -> Parser ()
punc cs = () <$ pspc <* plit cs <* pspc

pstring :: Parser String
pstring = Parser $ \ env str -> case str of
  '"' : str -> case span ('"' /=) str of
    (str, _:end) -> pure (str, end)
    _ -> []
  _ -> []

pnat :: Parser Int
pnat = Parser $ \ env str -> case span isDigit str of
  (ds@(_:_), str) -> [(read ds, str)]
  _ -> []

pnom :: Parser String
pnom = Parser $
  let isMo c = isAlphaNum c || elem c "_'" in
  \ env str -> case str of
  c : cs | isAlpha c -> case span isMo cs of
      (nm, str) -> [(c:nm, str)]
  _ -> []

pvar' :: Parser (String, Int)
pvar' = (,) <$> pnom <*> ((id <$ pch (== '^') <*> pnat) <|> pure 0)

pvar :: (String -> Parser a) -> (Int -> Parser a) -> Parser a
pvar str int = (either str int <=< pseek) =<< pvar'

patom :: Parser String
patom = pch (== '\'') *> pnom

-- | Returns whether a comment was found
pcom :: Parser Bool
pcom = Parser $ \ xs str -> pure $ case str of
  '{':'-':str -> (True, multiLine 1 str)
  '-':'-':str -> (True, singleLine str)
  _ -> (False, str)

  where

  multiLine 0 str = str
  multiLine n str = case dropWhile (`notElem` "{-") str of
    -- closing
    '-':'}':str -> multiLine (n-1) str
    -- starting
    '{':'-':str -> multiLine (1+n) str
    '-':'-':str -> multiLine n (singleLine str)
    -- false alarm: ignore the unrelated '-'/'{'
    _:str -> multiLine n str
    -- unclosed bracket which is fine by us
    [] -> []

  singleLine str = drop 1 $ dropWhile (/= '\n') str

-- Remove leading spaces, an optional comment, and repeat
pspc :: Parser ()
pspc = do
  Parser $ \ xs str -> [((),snd (span isSpace str))]
  b <- pcom
  if b then pspc else pure ()

pnl :: Parser ()
pnl = () <$ pch (\c -> c == '\n' || c == '\0')

psep :: Parser () -> Parser a -> Parser [a]
psep s p = (:) <$> p <*> many (id <$ s <*> p)
 <|> pure []

data ParserEnv
  = ParserEnv
  { objScope :: Bwd String
  , metaScopes :: MetaScopes
  }
type MetaScopes = Map String (Bwd String)

initParserEnv :: ParserEnv
initParserEnv = ParserEnv B0 Map.empty

data Parser a = Parser
  { parser :: ParserEnv -> String -> [(a, String)]
  }

penv :: Parser ParserEnv
penv = Parser $ \ env s -> [(env, s)]

instance Monad Parser where
  return a = Parser $ \ env s -> [(a, s)]
  Parser f >>= k = Parser $ \ env s -> do
    (a, s) <- f env s
    parser (k a) env s

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Functor Parser where
  fmap = ap . return

instance Alternative Parser where
  empty = Parser $ \ _ _ -> []
  Parser f <|> Parser g = Parser $ \ env s ->
    f env s ++ g env s

pbind :: String -> Parser a -> Parser a
pbind x (Parser p) = Parser $ \ env s ->
  p (env { objScope = objScope env :< x }) s

pmetasbind :: MetaScopes -> Parser a -> Parser a
pmetasbind als (Parser p) = Parser $ \ env s ->
  p (env { metaScopes = Map.union als (metaScopes env) }) s

pscope :: Parser (Bwd String)
pscope = objScope <$> penv

plen :: Parser Int
plen = length <$> pscope

plocal :: Bwd String -> Parser x -> Parser x
plocal xz (Parser p) = Parser $ \ env s -> p (env { objScope = xz }) s

ppop :: String -> Parser x -> Parser x
ppop x p = pscope >>= \case
  env :< y | x == y -> plocal env p
  _ -> empty

pmeta :: String -> Parser (Bwd String)
pmeta m = do
  ms <- metaScopes <$> penv
  case Map.lookup m ms of
    Just xz -> pure xz
    Nothing -> empty

pseek :: (String, Int) -> Parser (Either String Int)
pseek (x, n) = Parser $ \ env s -> let
  chug B0 n = [Left x]
  chug (xz :< y) n
    | y == x = if n == 0 then [Right 0] else fmap (1+) <$> chug xz (n - 1)
    | otherwise = fmap (1+) <$> chug xz n
  in (, s) <$> chug (objScope env) n

pch :: (Char -> Bool) -> Parser Char
pch p = Parser $ \ xz s -> case s of
  c : cs | p c -> [(c, cs)]
  _ -> []

pend :: Parser ()
pend = Parser $ \ xz s -> case s of
  [] -> [((), "")]
  _ -> []

parse :: Show x => Parser x -> String -> x
parse p s = case parser (id <$> p <* pend) initParserEnv s of
  [(x, _)] -> x
  x -> error (unlines $ "" : (show <$> x))

class Lisp t where
  mkNil  :: Int -> t
  mkCons :: t -> t -> t
  pCar   :: Parser t

plisp :: Lisp t => Parser t
plisp = mkNil <$ pch (== ']') <*> plen
    <|> id <$ pch (== '|') <* pspc <*> pCar <* pspc <* pch (== ']')
    <|> mkCons <$> pCar <* pspc <*> plisp
