{-# LANGUAGE OverloadedStrings #-}
module Pretty where

import ANSI hiding (withANSI)
import Bwd
import Doc
import Doc.Render.Terminal

-- TODO: use a structured Doc type as output
class Pretty a where
  pretty :: a -> Doc Annotations
  pretty = prettyPrec 0

  prettyPrec :: Int -> a -> Doc Annotations
  prettyPrec _ = pretty

escape :: String -> String
escape = concatMap go where

  go :: Char -> String
  go '\n' = "\\n"
  go '\t' = "\\t"
  go c = [c]

instance Pretty String where
  pretty s = text s

class Collapse t where
  collapse :: t (Doc Annotations) -> Doc Annotations

newtype BracesList t = BracesList { unBracesList :: [t] }

instance Collapse BracesList where
  collapse (BracesList ds) = braces $ hsepBy ";" ds

instance Collapse Bwd where
  collapse ds = brackets ("<" <+> hsepBy "," (ds <>> []))

instance Collapse [] where
  collapse ds = brackets (hsepBy "," ds)

instance Collapse Cursor where
  collapse (lstrs :<+>: rstrs) =
    hsep [ collapse lstrs
         , withANSI [SetColour Foreground Red, SetWeight Bold] ":<+>:"
         , collapse rstrs
         ]
