module Pretty where

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
