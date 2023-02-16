{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds #-}

module Location where

import ANSI hiding (withANSI)
import Data.List (foldl')
import System.FilePath
import Doc.Annotations
import Text.PrettyPrint.Compact
import Pretty (pretty)

data Location = Location
  { file :: FilePath
  , row :: !Int
  , col :: !Int
  } deriving (Eq, Ord)

instance Show Location where
  show (Location fp row col) = concat [takeFileName fp, ":", show row, ":", show col]

initLocation :: FilePath -> Location
initLocation fp = Location fp 1 0

-- Action of a character on a location
tick :: Location -> Char -> Location
tick l@Location{..} c =
  if c == '\n'
  then l { col = 0, row = row + 1 }
  else l { col = col + 1 }

ticks :: Location -> [Char] -> Location
ticks = foldl' tick

data Range = Range
  { source :: FilePath
  , start  :: !(Int, Int)
  , end    :: !(Int, Int)
  } deriving (Eq, Ord)

data WithRange t = WithRange
  { theRange :: Range
  , theValue :: t
  }

instance Show t => Show (WithRange t) where
  show = show . theValue

class HasSetRange t where
  setRange :: Range -> t -> t

class HasGetRange t where
  getRange :: t -> Range

instance HasGetRange Range where
  getRange = id

instance HasSetRange (WithRange t) where
  setRange r (WithRange _ t) = WithRange r t

instance HasGetRange (WithRange t) where
  getRange = theRange

type HasRange t = (HasSetRange t, HasGetRange t)

fromLocations :: Location -> Location -> Range
fromLocations s e = Range (file s) (row s, col s) (row e, col e)

addRange :: HasSetRange t => Location -> Location -> t -> t
addRange s e = setRange (fromLocations s e)

unknown :: Range
unknown = fromLocations invalid invalid where
  invalid = Location "" 0 0

instance Show Range where
  show r | r == unknown = "Unknown"
  show (Range fp (sr, sc) (er, ec)) =
    if sr == er
    then concat [takeFileName fp, ":", show sr, ":", show sc, "-", show ec]
    else concat [takeFileName fp, ":", show sr, ":", show sc, "-", show er, ":", show ec]

fileContext :: Range -> IO (Doc Annotations)
fileContext r
  | r == unknown = pure ""
  | fst (start r) /= fst (end r) = pure ""
  | otherwise = do
    content <- lines <$> readFile (source r)
    let focus = fst (start r)
    let begin = focus - 3
    let context = map pretty $ take 3 $ drop begin content
    let sizeHds = length (show focus)
    let display = \ n -> let header = show n in replicate (1 + sizeHds - length header) ' ' ++ header ++ " | "
    let headers = map (pretty . display) $ dropWhile (< 1) [begin+1..focus]
    let underline = pretty (replicate (sizeHds + 4 + snd (start r)) ' ')
                 <> withANSI [ SetWeight Bold, SetColour Foreground Red ]
                    (pretty (replicate (snd (end r) - snd (start r)) '^'))
    pure $ vcat $ "" : zipWith (<>) headers context ++ [underline, ""]

-- assuming things that have a valid range are ordered left-to-right
instance Semigroup Range where
  left <> right
    | left == unknown = right
    | right == unknown = left
    | otherwise = Range (source left) (start left) (end right)

instance Monoid Range where
  mempty = unknown
  mappend = (<>)
