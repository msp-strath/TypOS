module Format where

import Bwd
import Display
import Parse

-- | dir is a directive controlling the printing of terms
--   dbg is the type of debugging info available
data Format dir dbg t
  = TermPart dir t
  | DebugPart dbg
  | StringPart String
  deriving (Show, Eq, Functor, Foldable, Traversable)

data Directive = Instantiate | Raw
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
    (str, '%':'e':end) -> go end (snoc str acc :< DebugPart ShowEnv)
    (str, '%':'s':end) -> go end (snoc str acc :< DebugPart ShowStack)
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


instance Display Debug where
  display _ = \case
    ShowEnv -> "%e"
    ShowStack -> "%s"
    ShowStore -> "%m"

instance Display t => Display [Format Directive Debug t] where
  display na = go B0 B0 where

    go fmt args [] = unwords (('"' : concat fmt ++ ['"']) : args <>> [])
    go fmt args (f:fs) = case f of
      TermPart Raw t -> go (fmt :< "%r") (args :< pdisplay na t) fs
      TermPart Instantiate t -> go (fmt :< "%i") (args :< pdisplay na t) fs
      DebugPart dbg -> go (fmt :< pdisplay initNaming dbg) args fs
      StringPart str -> go (fmt :< concatMap escape str) args fs

    escape :: Char -> String
    escape '\n' = "\\n"
    escape '\t' = "\\t"
    escape c = [c]

instance Display t => Display [Format () String t] where
  display na = foldMap $ \case
    TermPart () t -> pdisplay na t
    DebugPart str -> str
    StringPart str -> str
