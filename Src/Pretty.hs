{-# LANGUAGE OverloadedStrings #-}
module Pretty where

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

newtype BracesList t = BracesList { unBracesList :: [t] }

instance Collapse BracesList where
  collapse (BracesList []) = "{}"
  collapse (BracesList ds) = usingConfig $ \ cfg -> case orientation cfg of
    Horizontal -> braces $ hsepBy ";" ds
    Vertical -> vcat (zipWith (<>) ("{" : repeat ";") ds) <> "}"

instance Collapse Bwd where
  collapse B0 = "[<]"
  collapse ds =  usingConfig $ \ cfg -> case orientation cfg of
    Horizontal -> brackets ("<" <> hsepBy "," (ds <>> []))
    Vertical -> vcat (zipWith (<>) ("[<" : repeat ",") (ds <>> [])) <> "]"

instance Collapse [] where
  collapse [] = "[]"
  collapse ds = usingConfig $ \ cfg -> case orientation cfg of
    Horizontal -> brackets (hsepBy "," ds)
    Vertical -> vcat (zipWith (<>) ("[" : repeat ",") ds) <> "]"

instance Collapse Cursor where
  collapse (lstrs :<+>: rstrs) = usingConfig $ \ cfg ->
    let osep = (case orientation cfg of { Horizontal -> hsep; Vertical -> vcat }) in
    osep [ collapse lstrs
         , withANSI [SetColour Foreground Red, SetWeight Bold] ":<+>:"
         , collapse rstrs
         ]
