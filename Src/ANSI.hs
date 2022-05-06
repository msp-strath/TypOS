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
