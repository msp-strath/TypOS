module Format where

import Data.Foldable
import Data.Traversable

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
  type DisplayEnv Debug = ()
  display = \case
    ShowEnv -> pure "%e"
    ShowStack -> pure "%s"
    ShowStore -> pure "%m"

instance Display Directive where
  type DisplayEnv Directive = ()
  display = \case
    Raw -> pure "%r"
    Instantiate -> pure "%i"

instance Display t => Display [Format Directive Debug t] where
  type DisplayEnv [Format Directive Debug t] = DisplayEnv t
  display = go B0 B0 where

    go fmt args [] = pure $ unwords (('"' : concat fmt ++ ['"']) : args <>> [])
    go fmt args (f:fs) = case f of
      TermPart d t -> do
        t <- pdisplay t
        d <- subdisplay d
        go (fmt :< d) (args :< t) fs
      DebugPart dbg -> do
        dbg <- subpdisplay dbg
        go (fmt :< dbg) args fs
      StringPart str -> go (fmt :< concatMap escape str) args fs

    escape :: Char -> String
    escape '\n' = "\\n"
    escape '\t' = "\\t"
    escape c = [c]

instance Display t => Display [Format () String t] where
  type DisplayEnv [Format () String t] = DisplayEnv t
  display f = (fold <$>) $ for f $ \case
    TermPart () t -> pdisplay t
    DebugPart str -> pure str
    StringPart str -> pure str
