module Parse where

import Control.Applicative
import Control.Monad

import Data.Bifunctor
import Data.Char
import Data.Function

import Bwd
import Location
import System.IO.Unsafe (unsafePerformIO)
import System.Exit (exitFailure)
import Data.List (intercalate)
import Data.Foldable (fold)

-- parsers, by convention, do not consume either leading
-- or trailing space

plit :: String -> Parser ()
plit cs = Expected ("'" ++ cs ++ "'") <!> mapM_ (pch . (==)) cs

punc :: String -> Parser ()
punc cs = () <$ pspc <* plit cs <* pspc

pparens :: Parser a -> Parser a
pparens p = id <$ pch (== '(') <* pspc <*> p <* pspc <* plit ")"

pcurlies :: Parser a -> Parser a
pcurlies p = id <$ punc "{" <*> p <* pspc <* plit "}"

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

psep1 :: Parser () -> Parser a -> Parser [a]
psep1 s p = (:) <$> p <* s <*> psep s p

psep :: Parser () -> Parser a -> Parser [a]
psep s p = (:) <$> p <*> many (id <$ s <*> p)
 <|> pure []

ppes :: Parser () -> Parser a -> Parser (Bwd a)
ppes s p = (B0 <><) <$> psep s p

data Source = Source
  { content :: String
  , location :: Location
  } deriving (Show)

data Hint = Expected String | Other String
  deriving (Show, Eq)

renderHints :: Bwd Hint -> String
renderHints descs =
  let (es, ds) = bimap fold fold $ flip unzipWith (nub descs) $ \case
        Expected str -> (B0 :< str, [])
        Other str -> (B0, [str])
  in
  let e = case es of
            B0 -> []
            B0 :< x -> ["Expected " ++ x ++ "."]
            xs :< x -> ["Expected " ++ intercalate ", " (xs <>> []) ++ ", or " ++ x ++ "."]
  in
  intercalate "\n" (e ++ ds)

data Candidate = Candidate
  { description :: Bwd Hint
  , candidateLoc :: Location
  }

instance Eq Candidate where (==) = (==) `on` candidateLoc

instance Semigroup Candidate where
  c1@(Candidate ds1 loc1) <> c2@(Candidate ds2 loc2) =
    case compare loc1 loc2 of
      LT -> c2
      EQ -> Candidate (ds1 <> ds2) loc1
      GT -> c1

newtype Parser a = Parser
  { parser :: Source -> (Candidate, [(a, Source)])
  }

pfail :: Parser a
pfail = Parser (notHere . location)

infix 0 <!>
(<!>) :: Hint -> Parser a -> Parser a
desc <!> p = Parser $ \ src ->
  let (Candidate mdesc loc, res) = parser p src in
  (Candidate (mdesc :< desc) loc, res)

here :: (a, Source) -> (Candidate, [(a, Source)])
here (a, s) = (Candidate B0 (location s), [(a, s)])

notHere :: Location -> (Candidate, [(a, Source)])
notHere loc = (Candidate B0 loc, [])

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
  empty = Parser (notHere . location)
  Parser f <|> Parser g = Parser $ \ s ->
    f s <> g s

pch :: (Char -> Bool) -> Parser Char
pch p = Parser $ \ (Source s loc) -> case s of
  c : cs | p c -> here (c, Source cs (tick loc c))
  _ -> notHere loc


pend :: Parser ()
pend = Parser $ \ i@(Source s loc) -> case s of
  [] -> here ((), i)
  _ -> notHere loc

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
  (Candidate ds loc, []) -> parseError Imprecise loc (renderHints ds)
  (Candidate _ loc, xs) -> parseError Imprecise loc (unlines ("Ambiguous parse:" : map (show . fst) xs))

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
  mkNil <$ plit "]"
  <|> id <$ plit "|" <* pspc <*> pCar <* pspc <* plit "]"
  <|> mkCons <$> pCar <* pspc <*> plisp
