module Location where
import Data.List (foldl')

data Location = Location
  { file :: FilePath
  , row :: !Int
  , col :: !Int
  } deriving (Eq, Ord)

instance Show Location where
  show (Location fp row col) = concat [fp, ":", show row, ":", show col]

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

class HasRange t where
  setRange :: Range -> t -> t
  getRange :: t -> Range

fromLocations :: Location -> Location -> Range
fromLocations s e = Range (file s) (row s, col s) (row e, col e)

addRange :: HasRange t => Location -> Location -> t -> t
addRange s e = setRange (fromLocations s e)

unknown :: Range
unknown = fromLocations invalid invalid where
  invalid = Location "" 0 0

instance Show Range where
  show r | r == unknown = "Unknown"
  show (Range fp (sr, sc) (er, ec)) =
    concat [fp, ":", show sr, ":", show sc, "-", show er, ":", show ec]
