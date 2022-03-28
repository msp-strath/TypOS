{-# LANGUAGE OverloadedStrings #-}
module Pretty where

import Data.Foldable
import Data.Void

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

keyword :: Doc Annotations -> Doc Annotations
keyword = withANSI [ SetUnderlining Single ]

escape :: String -> String
escape = concatMap go where

  go :: Char -> String
  go '\n' = "\\n"
  go '\t' = "\\t"
  go c = [c]

instance Pretty String where
  pretty s = text s

instance Pretty () where
  pretty _ = text "()"

instance Pretty Void where
  pretty = absurd

class Collapse t where
  collapse :: t (Doc Annotations) -> Doc Annotations
  vcollapse :: t (Doc Annotations) -> Doc Annotations

newtype BracesList t = BracesList { unBracesList :: [t] }

instance Collapse BracesList where
  collapse (BracesList ds) = braces $ hsepBy ";" ds

instance Collapse Bwd where
  collapse ds = brackets ("<" <+> hsepBy "," (ds <>> []))
  vcollapse ds = fold [ flush (vcat $ zipWith (<+>) ("[<": repeat ",") (ds <>> [])), "]" ]

instance Collapse [] where
  collapse ds = brackets (hsepBy "," ds)

instance Collapse Cursor where
  collapse (lstrs :<+>: rstrs) =
    hsep [ collapse lstrs
         , withANSI [SetColour Foreground Red, SetWeight Bold] ":<+>:"
         , collapse rstrs
         ]
