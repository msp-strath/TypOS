{-# LANGUAGE OverloadedStrings #-}
module Pretty
  ( module Text.PrettyPrint.Compact
  , module Doc.Annotations
  , Pretty(..)
  , Collapse(..)
  , BracesList(..)
  , asBlock
  , indent
  , keyword
  , escape
  , parenthesise
  , pipe
  ) where

import Data.Void

import ANSI hiding (withANSI)
import Bwd
import Doc.Annotations
import Text.PrettyPrint.Compact hiding (Options)

class Pretty a where
  pretty :: a -> Doc Annotations
  pretty = prettyPrec 0

  prettyPrec :: Int -> a -> Doc Annotations
  prettyPrec _ = pretty

indent :: Int ->  Doc Annotations -> Doc Annotations
indent n d = string (replicate n ' ') <> d

-- | asBlock n header lines
-- | @ n       the indentation for the block's line
-- | @ header  the title line of the block
-- | @ lines   the block's lines
asBlock :: Int -> Doc Annotations -> [Doc Annotations] -> Doc Annotations
asBlock n header [] = header
asBlock n header lines = header $$ vcat (map (indent n) lines)

parenthesise :: Bool -> Doc Annotations -> Doc Annotations
parenthesise True = parens
parenthesise False = id

keyword :: Doc Annotations -> Doc Annotations
keyword = withANSI [ SetUnderlining Single ]

pipe :: Doc Annotations
pipe = "|"

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

newtype BracesList t = BracesList { unBracesList :: [t] }

instance Collapse BracesList where
  collapse (BracesList []) = "{}"
  collapse (BracesList ds) = encloseSep "{" "}" "; " ds

instance Collapse Bwd where
  collapse B0 = "[<]"
  collapse ds =  encloseSep "<" "]" ", " (ds <>> [])

instance Collapse [] where
  collapse [] = "[]"
  collapse ds = encloseSep lbracket rbracket ", " ds

instance Collapse Cursor where
  collapse (lstrs :<+>: rstrs) =
    sep [ collapse lstrs
        , withANSI [SetColour Foreground Red, SetWeight Bold] ":<+>:"
        , collapse rstrs
        ]
