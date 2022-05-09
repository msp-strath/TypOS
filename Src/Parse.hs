module Parse where

import Control.Applicative
import Control.Monad

import Data.Bifunctor
import Data.Char
import Data.Semigroup

import Bwd
import Location
import System.IO.Unsafe (unsafePerformIO)
import System.Exit (exitFailure)

-- parsers, by convention, do not consume either leading
-- or trailing space

-- Future work: annotating (Max Location) with message
-- (<!>) :: String -> Parser a -> Parser a

plit :: String -> Parser ()
plit = mapM_ (pch . (==))

punc :: String -> Parser ()
punc cs = () <$ pspc <* plit cs <* pspc

pcurlies :: Parser a -> Parser a
pcurlies p = id <$ punc "{" <*> p <* pspc <* pch (== '}')

pstring :: Parser String
pstring = Parser $ \ (Source str loc) -> case str of
  '"' : str -> maybe (notHere loc) here (go str (tick loc '"'))
  _ -> notHere loc

  where

  go :: String -> Location -> Maybe (String, Source)
  go str loc =
    let (pref, end) = span (`notElem` "\\\"") str in
    let loc' = ticks loc pref in
    case end of
      '\\':'"':end -> first ((pref ++) . ('"' :)) <$> go end (ticks loc "\\\"")
      '\\':end -> first ((pref ++) . ('\\' :)) <$> go end (tick loc' '\\')
      '"':end -> pure (pref, Source end (tick loc' '\"'))
      _ -> Nothing


pnat :: Parser Int
pnat = Parser $ \ (Source str loc) -> case span isDigit str of
  (ds@(_:_), str) -> here (read ds, Source str (ticks loc ds))
  _ -> notHere loc

pnom :: Parser String
pnom = Parser $
  let isMo c = isAlphaNum c || elem c "_'" in
  \ (Source str loc) -> case str of
  c : cs | isAlpha c -> case span isMo cs of
      (nm, str) -> here (c:nm, Source str (ticks loc (c : nm)))
  _ -> notHere loc

patom :: Parser String
patom = pch (== '\'') *> pnom

-- | Returns whether a comment was found
pcom :: Parser Bool
pcom = Parser $ \ i@(Source str loc) -> here $ case str of
  '{':'-':str -> (True, multiLine 1 str (ticks loc "{-"))
  '-':'-':str -> (True, singleLine str (ticks loc "--"))
  _ -> (False, i)

  where

  multiLine :: Int -> String -> Location -> Source
  multiLine 0 str loc = Source str loc
  multiLine n str loc =
    let (pref, rest) = span (`notElem` "{-") str in
    let loc' = ticks loc pref in
    case rest of
      -- closing
      '-':'}':str -> multiLine (n-1) str (ticks loc' "-}")
      -- starting
      '{':'-':str -> multiLine (1+n) str (ticks loc' "{-")
      '-':'-':str ->
        let Source end loc'' = singleLine str (ticks loc' "--") in
        multiLine n end loc''
      -- false alarm: ignore the unrelated '-'/'{'
      c:str -> multiLine n str (tick loc' c)
      -- unclosed bracket which is fine by us
      [] -> Source [] loc'

  singleLine :: String -> Location -> Source
  singleLine str loc = case span (/= '\n') str of
    (cs, []) -> Source [] (ticks loc cs)
    (cs, d:ds) -> Source ds (tick (ticks loc cs) d)

-- Remove leading spaces, an optional comment, and repeat
pspc :: Parser ()
pspc = do
  Parser $ \ (Source str loc) ->
           let (cs, rest) = span isSpace str in
           here ((), Source rest (ticks loc cs))
  b <- pcom
  when b pspc

pnl :: Parser ()
pnl = () <$ pch (\c -> c == '\n' || c == '\0')

psep :: Parser () -> Parser a -> Parser [a]
psep s p = (:) <$> p <*> many (id <$ s <*> p)
 <|> pure []

ppes :: Parser () -> Parser a -> Parser (Bwd a)
ppes s p = (B0 <><) <$> psep s p

data Source = Source
  { content :: String
  , location :: Location
  } deriving (Show)

newtype Parser a = Parser
  { parser :: Source -> (Max Location, [(a, Source)])
  }

here :: (a, Source) -> (Max Location, [(a, Source)])
here (a, s) = (Max (location s), [(a, s)])

notHere :: Location -> (Max Location, [(a, Source)])
notHere loc = (Max loc, [])

ploc :: Parser Location
ploc = Parser $ \ i@(Source str loc) -> here (loc, i)

withRange :: HasRange t => Parser t -> Parser t
withRange p = do
   start <- ploc
   x <- p
   end <- ploc
   pure $ addRange start end x

instance Monad Parser where
  Parser f >>= k = Parser $ \ s ->
    let (loc, as) = f s in
    let (locs, bss) = unzip (map (\ (a, s) -> parser (k a) s) as) in
    (foldl1 (<>) (loc : locs), concat bss)

instance Applicative Parser where
  pure a = Parser $ here . (a ,)
  (<*>) = ap

instance Functor Parser where
  fmap = ap . return

instance Alternative Parser where
  empty = Parser $ \ s -> (Max (location s), [])
  Parser f <|> Parser g = Parser $ \ s ->
    f s <> g s

pch :: (Char -> Bool) -> Parser Char
pch p = Parser $ \ (Source s loc) -> case s of
  c : cs | p c -> here (c, Source cs (tick loc c))
  _ -> notHere loc

pend :: Parser ()
pend = Parser $ \ i@(Source s loc) -> (Max loc,) $ case s of
  [] -> [((), i)]
  _ -> []

data ErrorLocation = Precise | Imprecise

instance Show ErrorLocation where
  show Precise = "at"
  show Imprecise = "near"

parseError :: ErrorLocation -> Location -> String -> x
parseError prec loc str = unsafePerformIO $ do
  putStrLn ("Parse error " ++ show prec ++ " location: " ++ show loc ++ "\n" ++ str)
  exitFailure

parse :: Show x => Parser x -> Source -> x
parse p s = case parser (id <$> p <* pend) s of
  (_, [(x, _)]) -> x
  (loc, x) -> parseError Imprecise (getMax loc) (unlines $ "" : (show <$> x))

pmustwork :: String -> Parser x -> Parser x
pmustwork str p = Parser $ \ i -> case parser p i of
  (_, []) -> parseError Precise (location i) str
  res -> res

class Lisp t where
  mkNil  :: t
  mkCons :: t -> t -> t
  pCar   :: Parser t

plisp :: (Lisp t, HasRange t) => Parser t
plisp = withRange $
  mkNil <$ pch (== ']')
  <|> id <$ pch (== '|') <* pspc <*> pCar <* pspc <* pch (== ']')
  <|> mkCons <$> pCar <* pspc <*> plisp
