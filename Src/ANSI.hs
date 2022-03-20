module ANSI where

import Data.List (intercalate)

import System.IO.Unsafe

data Colour
  = Black | Red | Green | Yellow | Blue
  | Magenta | Cyan | White
  deriving (Show, Enum)

data Layer
  = Foreground | Background

data Weight
  = Bold | Faint | Normal
  deriving (Show)

data Underlining
  = Single | Double
  deriving (Show)

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

alarm :: String -> a -> a
alarm str x = unsafePerformIO $ do
  putStrLn $ withANSI [SetColour Background Red] "Alarm:" ++ ' ' : str
  _ <- getLine
  pure x
