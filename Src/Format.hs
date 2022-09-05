module Format where

import Bwd
import Parse
import Location

-- | dir is a directive controlling the printing of terms
--   dbg is the type of debugging info available
data Format dir dbg t
  = TermPart dir t
  | DebugPart dbg
  | StringPart String
  deriving (Show, Eq, Functor, Foldable, Traversable)

data Directive = Normalise | Instantiate | Raw | ShowT
 deriving (Show, Eq)

data Debug = ShowStack | ShowStore | ShowEnv
  deriving (Show, Eq)

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
