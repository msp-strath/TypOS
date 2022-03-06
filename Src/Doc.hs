{-# LANGUAGE OverloadedStrings #-}

-- Module based on Jean-Philippe Bernardy's functional pearl
-- "A Pretty But Not Greedy Printer"
-- (or rather my Agda port of it in the stdlib's Text.Pretty)

module Doc where

import Data.Function
import Data.List
import Data.String
import GHC.Stack

import Doc.Internal (Block)
import qualified Doc.Internal as I

class DocConfig cfg where
  tapeWidth :: Doc cfg -> Int

newtype Doc cfg = Doc { runDoc :: [Block] }

instance IsString (Doc cfg) where
  fromString str = Doc [I.text str]

cutOff :: DocConfig cfg => Doc cfg -> Doc cfg
cutOff doc@(Doc ds) = Doc (filter ((tapeWidth doc >=) . I.maxWidth) ds)

render :: Doc cfg -> String
render (Doc []) = ""
render (Doc ds) = I.render $ minimumBy (compare `on` I.height) ds

fail :: Doc cfg
fail = Doc []

-- Should we fail or not for literals that are too big?
text :: (HasCallStack, DocConfig cfg) => String -> Doc cfg
text str = case cutOff (fromString str) of
  Doc [] -> error ("String too long :" ++ show str)
  doc -> doc

instance DocConfig cfg => Semigroup (Doc cfg) where
  Doc bs1 <> Doc bs2 = cutOff $ Doc ((<>) <$> bs1 <*> bs2)

empty :: Doc cfg
empty = Doc [I.text ""]

indent :: DocConfig cfg => Int -> Doc cfg -> Doc cfg
indent n d = spaces n <> d

instance DocConfig cfg => Monoid (Doc cfg) where
  mempty = empty

(<+>) :: DocConfig cfg => Doc cfg -> Doc cfg -> Doc cfg
d <+> e = d <> space <> e

char :: Char -> Doc cfg
char c = Doc [I.text [c]]

spaces :: Int -> Doc cfg
spaces i = Doc [I.text (replicate i ' ')]

semi = char ';'
colon = char ':'
comma = char ','
space = char ' '
dot = '.'

backslash = char '\\'
forwardslash = char '/'
equal = char '='

squote = char '\''
dquote = char '"'

lparen = char '('
rparen = char ')'
langle = char '<'
rangle = char '>'

lbrace = char '{'
rbrace = char '}'

lbracket = char '['
rbracket = char ']'

flush :: Doc cfg -> Doc cfg
flush (Doc ds) = Doc (I.flush <$> ds)

($$) :: DocConfig cfg => Doc cfg -> Doc cfg -> Doc cfg
d $$ e = flush d <> e

alts :: [Doc cfg] -> Doc cfg
alts ds = Doc (concatMap runDoc ds)

foldDoc :: (Doc cfg -> Doc cfg -> Doc cfg) -> [Doc cfg] -> Doc cfg
foldDoc c [] = empty
foldDoc c [x] = x
foldDoc c (x : xs) = c x (foldDoc c xs)

hsep :: DocConfig cfg => [Doc cfg] -> Doc cfg
hsep = foldDoc (<+>)

hsepBy :: DocConfig cfg => Doc cfg -> [Doc cfg] -> Doc cfg
hsepBy s = foldDoc (\x y -> x <> s <+> y)

vcat :: DocConfig cfg => [Doc cfg] -> Doc cfg
vcat = foldDoc ($$)

sep :: DocConfig cfg => [Doc cfg] -> Doc cfg
sep [] = empty
sep ds = alts [hsep ds, vcat ds]

between :: DocConfig cfg => Doc cfg -> Doc cfg -> Doc cfg -> Doc cfg
between d f e = d <> e <> f

parens :: DocConfig cfg => Doc cfg -> Doc cfg
parens = between lparen rparen

parenthesise :: DocConfig cfg => Bool -> Doc cfg -> Doc cfg
parenthesise b = if b then parens else id

newline :: Doc cfg
newline = flush empty

softline :: Doc cfg
softline = alts [space, newline]

{-
matrix :: (a -> Doc ()) -> [[a]] -> Doc ()
matrix cell
  = indent 2
  . vcat
  . ((text "i\\j" <+> foldDoc (\x y -> x <> indent 2 y) (map (text . show) [0..7])) :)
  . zipWith (\ x y -> x <> indent 2 y) (map (text . show) [0..])
  . map ( between lbracket rbracket
        . hsepBy comma
        . map cell
        )

instance DocConfig () where
  tapeWidth _ = 8000

testMatrix :: [[Bool]]
testMatrix = do
  i <- [1..10]
  pure $ do
    j <- [1..8]
    pure (j `mod` i /= 0)

test = putStr $ render (matrix (\ b -> char (if b then '1' else '0')) testMatrix)
-}
