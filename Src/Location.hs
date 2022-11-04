{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds #-}

{- | Description: The concept of a location within a file.
   Also defines the concept of a Range (within a file) and what
   amounts to a lens for it.
-}
module Location (
    Location, initLocation
  , tick, ticks
  , Range, WithRange(..), HasRange, addRange, HasGetRange(getRange), HasSetRange(setRange)
  , unknown
  , fileContext
  ) where

import ANSI (Annotation(..), Weight(..), Layer(..), Colour(..))
import Data.List (foldl')
import System.FilePath (takeFileName)
import Doc.Annotations (Annotations, withANSI)
import Text.PrettyPrint.Compact (Doc, vcat)
import Pretty (pretty)

{- | A 'Location' in a file (specified via a 'FilePath') is a 'row' and 'column'.
   This implicitly tells us that the contents of files are treated as being
   made up of rows which themselves are made up of columns. It's probably understood
   that these are of "some kind of text".
-}
data Location = Location
  { file :: FilePath -- the file in which we have a location
  , row :: !Int      -- a specific row
  , col :: !Int      -- a specific column
  } deriving (Eq, Ord)

-- | Print locations
instance Show Location where
  show (Location fp row col) = concat [takeFileName fp, ":", show row, ":", show col]

-- | The initial location is the 1rst line, 0th character
initLocation :: FilePath -> Location
initLocation fp = Location fp 1 0

-- Action of a character on a location, i.e. advance by 1
-- Order of parameters "flipped" from the description for the purposes of 'foldl''
tick :: Location -> Char -> Location
tick l@Location{..} c =
  if c == '\n'
  then l { col = 0, row = row + 1 }
  else l { col = col + 1 }

-- Action of a list of characters on a location.
ticks :: Location -> [Char] -> Location
ticks = foldl' tick

-- A 'Range' in a file is equivalent to a pair of 'Location' into the same
-- file. But that representation would too easily violate the "same file"
-- invariant, and so this representation is more foolproof.
data Range = Range
  { source :: FilePath
  , start  :: !(Int, Int)
  , end    :: !(Int, Int)
  } deriving (Eq, Ord)

-- This is really an attributed value, i.e. a value decorated with a 'Range'
data WithRange t = WithRange
  { theRange :: Range
  , theValue :: t
  }

-- Showing a 'WithRange' ignores the range and just shows the value.
instance Show t => Show (WithRange t) where
  show = show . theValue

-- Setter for structures attributed with a Range
class HasSetRange t where
  setRange :: Range -> t -> t

-- Getter for structures attributed with a Range
class HasGetRange t where
  getRange :: t -> Range

-- 'WithRange' has a setter
instance HasSetRange (WithRange t) where
  setRange r (WithRange _ t) = WithRange r t

-- 'WithRange' and a getter
instance HasGetRange (WithRange t) where
  getRange = theRange

-- 'HasRange' is essentially a "classy lens" (without the baggage)
type HasRange t = (HasSetRange t, HasGetRange t)

-- Warning: fragile. Take two 'Location', assume that the second one
-- is for the same file. Hard error if this is not correct.
fromLocations :: Location -> Location -> Range
fromLocations s e = 
  if not (file s == file e) then error "Trying to make a Range from incompatible locations"
  else Range (file s) (row s, col s) (row e, col e)

-- Set the range of an attributed value from one created from 2 locations (fragile)
addRange :: HasRange t => Location -> Location -> t -> t
addRange s e = setRange (fromLocations s e)

-- An 'unknown' (invalid) range in a non-existent file. This is mainly used for the Monoid
-- instance.
unknown :: Range
unknown = Range "" (0,0) (0,0)

-- Show the range. Be smart if they both start in the same place.
instance Show Range where
  show r | r == unknown = "Unknown"
  show (Range fp (sr, sc) (er, ec)) =
    if sr == er
    then concat [takeFileName fp, ":", show sr, ":", show sc, "-", show ec]
    else concat [takeFileName fp, ":", show sr, ":", show sc, "-", show er, ":", show ec]

-- grab 3 lines before and after a 'Range' from a file, and pretty-print it.
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
