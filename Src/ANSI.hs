{-|
Description: For decorating the output with colour, font weight, etc

Support a variety of annotations (colour, font weight and underlining) that
can apply to different layers.

Note that the rest of the code (currently) uses explicit colour names to get
its work done.
 -}
module ANSI where

import Data.List (intercalate)

data Colour
  = Black | Red | Green | Yellow | Blue
  | Magenta | Cyan | White
  deriving (Eq, Show, Enum)

data Layer
  = Foreground | Background

data Weight
  = Bold | Faint | Normal
  deriving (Eq, Show)

data Underlining
  = Single | Double
  deriving (Eq, Show)

data Annotation
  = SetColour Layer Colour
  | SetWeight Weight
  | SetUnderlining Underlining

-- | The "magic" of how to get a terminal to output annotated text is
-- only known inside this function.  Similarly for the details of the
-- meaning of 'weight' and 'layer'
withANSI :: [Annotation] -> String -> String
withANSI [] str = str
withANSI anns str = concat
  [ "\x1b[", intercalate ";" (show . encode <$> anns) , "m"
  , str
  , "\x1b[0m" ]

  where

    encode (SetColour l c) = layer l + colour c
    encode (SetWeight w) = weight w
    encode (SetUnderlining u) = underlining u

    layer Foreground = 30
    layer Background = 40

    colour = fromEnum

    weight Bold = 1
    weight Faint = 2
    weight Normal = 22

    underlining Single = 4
    underlining Double = 21
