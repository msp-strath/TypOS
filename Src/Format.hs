module Format where

import Bwd
import Parse

-- | dir is a directive controlling the printing of terms
--   dbg is the type of debugging info available
data Format dir dbg t
  = TermPart dir t
  | DebugPart dbg
  | StringPart String
  deriving (Show, Eq, Functor, Foldable, Traversable)

data Directive = Instantiate | Raw | ShowT
 deriving (Show, Eq)

data Debug = ShowStack | ShowStore | ShowEnv
  deriving (Show, Eq)


pformat :: Parser [Format Directive Debug ()]
pformat = Parser $ \ env str -> case str of
  '"':str -> [go str B0]
  _ -> []

  where

  snoc :: String -> Bwd (Format Directive Debug ()) -> Bwd (Format Directive Debug ())
  snoc "" acc = acc
  -- hopefully there aren't too many of these
  snoc str (acc :< StringPart strl) = acc :< StringPart (strl ++ str)
  snoc str acc = acc :< StringPart str

  go :: String -> Bwd (Format Directive Debug ()) -> ([Format Directive Debug ()], String)
  go str acc = case span (`notElem` "%\"\\") str of
    -- formatting expressions
    (str, '%':'r':end) -> go end (snoc str acc :< TermPart Raw ())
    (str, '%':'i':end) -> go end (snoc str acc :< TermPart Instantiate ())
    (str, '%':'s':end) -> go end (snoc str acc :< TermPart ShowT ())
    (str, '%':'e':end) -> go end (snoc str acc :< DebugPart ShowEnv)
    (str, '%':'S':end) -> go end (snoc str acc :< DebugPart ShowStack)
    (str, '%':'m':end) -> go end (snoc str acc :< DebugPart ShowStore)
    -- special characters
    (str, '\\':'n':end) -> go end (snoc (str ++ "\n") acc)
    (str, '\\':'t':end) -> go end (snoc (str ++ "\t") acc)
    -- escaped characters
    (str, '\\':c:end) -> go end (snoc (str ++ [c]) acc)
    -- closing double quote
    (str, '"':end)     -> (snoc str acc <>> [], end)
    -- error
    (_, _) -> error "Unclosed format string"
