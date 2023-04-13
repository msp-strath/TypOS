{- Description: Parser utilities for the external syntax -}
module Parse where

import Control.Applicative (Alternative(..))
import Control.Monad (when, ap)

import Data.Bifunctor (first, bimap)
import Data.Char (isSpace, isAlphaNum, isAlpha, isDigit)
import Data.Function (on)
import Data.These (These(..))

import Bwd (Bwd(..),(<><), unzipWith, nub, (<>>))
import Location (Location, HasSetRange, WithRange(WithRange), tick, ticks, addRange, unknown)
import System.IO.Unsafe (unsafePerformIO)
import System.Exit (exitFailure)
import Data.List (intercalate)
import Data.Foldable (fold)

-- Even though Haskell does not require this, the functions below
-- are nevertheless mostly ordered by dependency.

----------------------------------------------------------------------
-- | A 'Source' is some content (as a String) which comes from a 'Location'
data Source = Source
  { content :: String    -- what we're parsing
  , location :: Location -- where it came from
  } deriving (Show)

----------------------------------------------------------------------
-- | A 'Hint' is either what we expect, or something else.
-- These 'Expected' is used to give better error messages when we encounter something
-- that is not expected.
data Hint = Expected String | Other String
  deriving (Show, Eq)

-- | Hints usually come as (snoc) lists, and we want to show them nicely
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

----------------------------------------------------------------------
-- | A Candidate is a 'Location' as well as a (snoc) list of 'Hint's.
data Candidate = Candidate
  { description :: Bwd Hint
  , candidateLoc :: Location
  }

-- | Candidates are equal when they are in the same place
instance Eq Candidate where (==) = (==) `on` candidateLoc

-- | The 'Semigroup' structure is induced by the order.
instance Semigroup Candidate where
  c1@(Candidate ds1 loc1) <> c2@(Candidate ds2 loc2) =
    case compare loc1 loc2 of
      LT -> c2
      EQ -> Candidate (ds1 <> ds2) loc1
      GT -> c1

----------------------------------------------------------------------
-- Where are the candidates for a parse?

-- | here says that what we want to parse is located 'here'
-- (and, implicitly, that there is just one of them)
here :: (a, Source) -> (Candidate, [(a, Source)])
here (a, s) = (Candidate B0 (location s), [(a, s)])

-- | notHere says that whatever is here, is not what we want
notHere :: Location -> (Candidate, [(a, Source)])
notHere loc = (Candidate B0 loc, [])

----------------------------------------------------------------------
-- Conventions:
-- - parsers do not consume either leading or trailing space
-- - pieces of parsers start with 'p' in their name.
-- - documentation below will not say "parse X", just X

-- | A 'Parser' for type a is a function from a 'Source' to a pair of a 'Candidate' (parse)
-- and a list of (a, Source), i.e. a list of successes and remainders.
newtype Parser a = Parser
  { parser :: Source -> (Candidate, [(a, Source)])
  }

-- Parsers have a lot of structure: Alternative Monads.
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

----------------------------------------------------------------------
-- And now for some actual parsers

-- | Collection of characters, given by a selection function
pch :: (Char -> Bool) -> Parser Char
pch p = Parser $ \ (Source s loc) -> case s of
  c : cs | p c -> here (c, Source cs (tick loc c))
  _ -> notHere loc

-- | Annotation a 'Parser' with a 'Hint'
infix 0 <!>
(<!>) :: Hint -> Parser a -> Parser a
desc <!> p = Parser $ \ src ->
  let (Candidate mdesc loc, res) = parser p src in
  (Candidate (mdesc :< desc) loc, res)

-- | literals; make sure to remember what is actually expected.
plit :: String -> Parser ()
plit cs = Expected ("'" ++ cs ++ "'") <!> mapM_ (pch . (==)) cs

-- | Returns whether a comment was found, and leave lots of
-- information about the comment in the location
pcom :: Parser Bool
pcom = Parser $ \ i@(Source str loc) -> here $ case str of
  '{':'-':str -> (True, multiLine 1 str (ticks loc "{-"))
  '-':'-':str -> (True, singleLine str (ticks loc "--"))
  _ -> (False, i)

  where

  -- | Parse multi-line comments
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

  -- | Parse single line comments
  singleLine :: String -> Location -> Source
  singleLine str loc = case span (/= '\n') str of
    (cs, []) -> Source [] (ticks loc cs)
    (cs, d:ds) -> Source ds (tick (ticks loc cs) d)

-- | Remove leading spaces, an optional comment, and repeat
pspc :: Parser ()
pspc = do
  Parser $ \ (Source str loc) ->
           let (cs, rest) = span isSpace str in
           here ((), Source rest (ticks loc cs))
  b <- pcom
  when b pspc

-- | Remove comments; if no comment present, a single space, then more.
pspc1 :: Parser ()
pspc1 = do
  b <- pcom
  when (not b) $ () <$ pch isSpace
  pspc

-- | punctuation, as a String, which does swallow spaces
-- This is used for expected punctuation rather than optional.
ppunc :: String -> Parser ()
ppunc cs = () <$ pspc <* plit cs <* pspc

-- | get something that is within parentheses. Note that
-- if we do get an opening parens, then we *expect* a closing
-- one (i.e. 'pch' versus 'plit')
pparens :: Parser a -> Parser a
pparens p = id <$ pch (== '(') <* pspc <*> p <* pspc <* plit ")"

-- | get something within curlies, at a point where we're expecting them
--   NB: we are exceptionally consuming leading space here!
pcurlies :: Parser a -> Parser a
pcurlies p = id <$ ppunc "{" <*> p <* pspc <* plit "}"

-- | for literal strings, i.e. enclosed in double-quotes.
-- The code is complicated because of escapes and escaped quotes.
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

-- | Digits into Int
pnat :: Parser Int
pnat = Parser $ \ (Source str loc) -> case span isDigit str of
  (ds@(_:_), str) -> here (read ds, Source str (ticks loc ds))
  _ -> notHere loc

-- | Names (nom is the French for that) allow an alphabetic character
-- followed by alphanumeric, underscore or quote.
pnom :: Parser String
pnom = Parser $
  let isMo c = isAlphaNum c || elem c "_'" in
  \ (Source str loc) -> case str of
  c : cs | isAlpha c -> case span isMo cs of
      (nm, str) -> here (c:nm, Source str (ticks loc (c : nm)))
  _ -> notHere loc

-- | an Atom is signalled by putting a single quote in front of a name
patom :: Parser String
patom = pch (== '\'') *> pnom

-- | remove newlines (and nulls)
pnl :: Parser ()
pnl = () <$ pch (\c -> c == '\n' || c == '\0')

-- | For a list of things of type a with a separator
psep :: Parser () -> Parser a -> Parser [a]
psep s p = (:) <$> p <*> many (id <$ s <*> p)
 <|> pure []

-- | For a non-empty list of things of type a with a separator
psep1 :: Parser () -> Parser a -> Parser [a]
psep1 s p = (:) <$> p <* s <*> psep s p

-- | For a snoc list of separated list of a
ppes :: Parser () -> Parser{--}a -> Parser (Bwd a)
ppes s p = (B0 <><) <$> psep s p

-- | The always failing parser
pfail :: Parser a
pfail = Parser (notHere . location)

-- | Extract the location of where we are, i.e. reify it
ploc :: Parser Location
ploc = Parser $ \ i@(Source str loc) -> here (loc, i)

-- | Given a parser of things that have ranges, make sure
-- to reify those when parsing.
withRange :: HasSetRange t => Parser t -> Parser t
withRange p = do
   start <- ploc
   x <- p
   end <- ploc
   pure $ addRange start end x

-- | Decorate something with a range when parsing it (if possible)
pwithRange :: Parser a -> Parser (WithRange a)
pwithRange p = withRange (WithRange unknown <$> p)

-- | Are we at the end of the thing we're parsing?
pend :: Parser ()
pend = Parser $ \ i@(Source s loc) -> case s of
  [] -> here ((), i)
  _ -> notHere loc

----------------------------------------------------------------------
-- Dealing with errors

-- | How well do we know where the error occured?
data ErrorLocation = Precise | Imprecise

-- | Turn our precision information into English
instance Show ErrorLocation where
  show Precise = "at"
  show Imprecise = "near"

-- | Hard-erroring out with a parse error
parseError :: ErrorLocation -> Location -> String -> x
parseError prec loc str = unsafePerformIO $ do
  putStrLn ("Parse error " ++ show prec ++ " location: " ++ show loc ++ "\n" ++ str)
  exitFailure

----------------------------------------------------------------------
-- Running an actual parser
parse :: Show x => Parser x -> Source -> x
parse p s = case parser (id <$> p <* pend) s of
  (_, [(x, _)]) -> x
  (Candidate ds loc, []) -> parseError Imprecise loc (renderHints ds)
  (Candidate _ loc, xs) -> parseError Imprecise loc (unlines ("Ambiguous parse:" : map (show . fst) xs))

-- Parsing something which we think we already know what it is
pmustwork :: String -> Parser x -> Parser x
pmustwork str p = Parser $ \ i -> case parser p i of
  (_, []) -> parseError Precise (location i) str
  res -> res

----------------------------------------------------------------------
-- A Lispy thing is something that has nil, cons, and a parser
class Lisp t where
  mkNil  :: t
  mkCons :: t -> t -> t
  pCar   :: Parser t

-- | Parse a lispy language, with an optional transformer
plisp :: (Lisp t, HasSetRange t) => Parser t
plisp = withRange $
  mkNil <$ plit "]"
  <|> id <$ plit "|" <* pspc <*> pCar <* pspc <* plit "]"
  <|> mkCons <$> pCar <* pspc <*> plisp

-- | Attempt to parse an input as two things
pthese :: Parser a -> Parser b -> Parser (These a b)
pthese pa pb = Parser $ \ i -> case (parser pa i, parser pb i) of
  ((c, [(a, rest)]), (_, [])) -> (c, [(This a, rest)])
  ((_, []), (c, [(b, rest)])) -> (c, [(That b, rest)])
  ((c1, [(a, rest1)]), (c2, [(b, rest2)])) | location rest1 == location rest2 ->
    (c1 <> c2, [(These a b, rest1)])
  ((c1, as), (c2, bs)) -> (c1 <> c2, [ (This a, rs) | (a, rs) <- as] ++ [ (That b, rs) | (b, rs) <- bs])

{-
plisp :: (Lisp t, HasRange t) => Maybe (Parser t -> Parser t) -> Parser t
plisp tr = maybe (doit id) (doit) tr
  where
    doit :: (Lisp t, HasRange t) => (Parser t -> Parser t) -> Parser t
    doit tr = id <$ pch (== '[') <* pspc <*> tr (withRange $
      mkNil <$ plit "]"
      <|> id <$ plit "|" <* pspc <*> pCar <* pspc <* plit "]"
      <|> mkCons <$> pCar <* pspc <*> plisp Nothing)
-}
