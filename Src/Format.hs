module Format where
{- Description: various utilities for nicely "format strings" that
 - can direct how to print terms, debugging info and just plain text
 
 In particular:
 For terms
  - %r - Raw
  - %i - Instantiate
  - %n - Normalize
  - %s - Show
 For Debugging:
  - %E - show environment
  - %S - show stack
  - %M - show store
-}

import Bwd (Bwd(..), (<>>))
import Parse (Parser(Parser), Source(Source), parseError, ErrorLocation(Precise), here, notHere)
import Location (Location, tick, ticks)

-- | Format specifiction, where
-- - dir is a directive controlling the printing of terms
-- - dbg is the type of debugging info available
-- - t is the actual term
data Format dir dbg t
  = TermPart dir t    -- for formatting terms
  | DebugPart dbg     -- for debugging
  | StringPart String -- for random stuff?
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | When printing terms, what to do with them when doing so
data Directive = Normalise | Instantiate | Raw | ShowT
 deriving (Show, Eq)

-- | When printing debug information, what to dump
data Debug = ShowStack | ShowStore | ShowEnv
  deriving (Show, Eq)

-- | Parse format specification, for but terms and debug
pformat :: Parser [Format Directive Debug ()]
pformat = Parser $ \ (Source str loc) -> case str of
  '"':str -> here (go str (tick loc '"') B0)
  _ -> notHere loc

  where

  snoc :: String -> Bwd (Format Directive Debug ()) -> Bwd (Format Directive Debug ())
  snoc "" acc = acc
  -- hopefully there aren't too many of these
  snoc str (acc :< StringPart strl) = acc :< StringPart (strl ++ str)
  snoc str acc = acc :< StringPart str

  go :: String -> Location -> Bwd (Format Directive Debug ()) -> ([Format Directive Debug ()], Source)
  go str loc acc =
    let (pref, rest) = span (`notElem` "%\"\\") str in
    let loc' = ticks loc pref in
    case rest of
    -- formatting expressions
    '%':'r':end -> go end (ticks loc' "%r") (snoc pref acc :< TermPart Raw ())
    '%':'i':end -> go end (ticks loc' "%i") (snoc pref acc :< TermPart Instantiate ())
    '%':'n':end -> go end (ticks loc' "%n") (snoc pref acc :< TermPart Normalise ())
    '%':'s':end -> go end (ticks loc' "%s") (snoc pref acc :< TermPart ShowT ())
    '%':'E':end -> go end (ticks loc' "%E") (snoc pref acc :< DebugPart ShowEnv)
    '%':'S':end -> go end (ticks loc' "%S") (snoc pref acc :< DebugPart ShowStack)
    '%':'M':end -> go end (ticks loc' "%M") (snoc pref acc :< DebugPart ShowStore)
    '%':end     -> go end (tick loc' '%')   (snoc (pref ++ "%") acc)
    -- special characters
    '\\':'n':end -> go end (ticks loc' "\\n") (snoc (pref ++ "\n") acc)
    '\\':'t':end -> go end (ticks loc' "\\t") (snoc (pref ++ "\t") acc)
    -- escaped characters
    '\\':c:end -> go end (tick loc' '\\') (snoc (pref ++ [c]) acc)
    -- closing double quote
    '"':end     -> (snoc pref acc <>> [], Source end (tick loc' '"'))
    -- error
    _ -> parseError Precise loc "Unclosed format string"
