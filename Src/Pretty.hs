module Pretty where

import ANSI
import Bwd
import Data.List

-- TODO: use a structured Doc type as output
class Pretty a where
  pretty :: a -> String
  pretty = prettyPrec 0

  prettyPrec :: Int -> a -> String
  prettyPrec _ = pretty

parens :: String -> String
parens str = concat ["(", str, ")"]

parenthesise :: Bool -> String -> String
parenthesise b = if b then parens else id

brackets :: String -> String
brackets str = concat ["[", str, "]"]

braces :: String -> String
braces str = concat ["{", str, "}"]

escape :: String -> String
escape = concatMap go where

  go :: Char -> String
  go '\n' = "\\n"
  go '\t' = "\\t"
  go c = [c]

instance Pretty String where
  pretty s = s

class Collapse t where
  collapse :: t String -> String

newtype BracesList t = BracesList { unBracesList :: [t] }

instance Collapse BracesList where
  collapse (BracesList strs) = "{" ++ intercalate "; " strs ++ "}"

instance Collapse Bwd where
  collapse strs = "[<" ++ intercalate ", " (strs <>> []) ++ "]"

instance Collapse [] where
  collapse strs = "[" ++ intercalate ", " strs ++ "]"

instance Collapse Cursor where
  collapse (lstrs :<+>: rstrs) =
    unwords [ collapse lstrs
            , withANSI [SetColour Foreground Red, SetWeight Bold] ":<+>:"
            , collapse rstrs
            ]
