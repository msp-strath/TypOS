{-|
Description: The internals of pretty-printing.
-}
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

import Data.Void (Void, absurd)

import ANSI hiding (withANSI)
import Bwd (Bwd(..),Cursor(..),(<>>))
import Doc.Annotations (Annotations,withANSI,toANSIs) -- will be re-exported?
import Text.PrettyPrint.Compact hiding (Options) -- will be re-exported from here

-- | Class Pretty lets us declare what things are (nicely) printable.
class Pretty a where
  pretty :: a -> Doc Annotations
  pretty = prettyPrec 0

  prettyPrec :: Int -> a -> Doc Annotations
  prettyPrec _ = pretty

-- | Indent by 'n' spaces
indent :: Int ->  Doc Annotations -> Doc Annotations
indent n d = string (replicate n ' ') <> d

-- | asBlock n header lines
-- | @ n       the indentation for the block's line
-- | @ header  the title line of the block
-- | @ lines   the block's lines
asBlock :: Int -> Doc Annotations -> [Doc Annotations] -> Doc Annotations
asBlock n header [] = header
asBlock n header lines = header $$ vcat (map (indent n) lines)

-- | maybe 'parenthesize' a document
parenthesise :: Bool -> Doc Annotations -> Doc Annotations
parenthesise True = parens
parenthesise False = id

-- | keywords are underlined
keyword :: Doc Annotations -> Doc Annotations
keyword = withANSI [ SetUnderlining Single ]

-- | 'pipe' symbol
pipe :: Doc Annotations
pipe = "|"

-- | 'escape' goes through a 'String' and escape carriage return and tab
escape :: String -> String
escape = concatMap go where

  go :: Char -> String
  go '\n' = "\\n"
  go '\t' = "\\t"
  go c = [c]

-- Instances for some common types

instance Pretty String where
  pretty s = text s

instance Pretty () where
  pretty _ = text "()"

instance Pretty Void where
  pretty = absurd

------------------------------------------------------------------
-- | a 't's worth of |Doc| can be 'Collapse'd if it can be flattened to a 'Doc'
class Collapse t where
  collapse :: t (Doc Annotations) -> Doc Annotations

-- | print snoc lists as "[< a , b , c ]", and the empty one as "[<]"
instance Collapse Bwd where
  collapse ds =  encloseSep "[<" "]" ", " (ds <>> [])

-- | print lists as usual
instance Collapse [] where
  collapse ds = encloseSep lbracket rbracket ", " ds

-- | print 'Cursor' with a Bold Red ":<+>:" in the middle
instance Collapse Cursor where
  collapse (lstrs :<+>: rstrs) =
    sep [ collapse lstrs
        , withANSI [SetColour Foreground Red, SetWeight Bold] ":<+>:"
        , collapse rstrs
        ]

-- | 'BracesList' is a marker for printing something in braces
newtype BracesList t = BracesList { unBracesList :: [t] }

-- | print 'BracesList' as lists with braces...
instance Collapse BracesList where
  collapse (BracesList ds) = encloseSep "{" "}" "; " ds
