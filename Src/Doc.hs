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
  tapeWidth :: Doc cfg ann -> Int

newtype Doc cfg ann = Doc { runDoc :: [Block ann] }

instance Functor (Doc cfg) where
  fmap f (Doc ds) = Doc (map (f <$>) ds)

instance Monoid ann => IsString (Doc cfg ann) where
  fromString str = Doc [I.text str]

cutOff :: DocConfig cfg => Doc cfg ann -> Doc cfg ann
cutOff doc@(Doc ds) = Doc (filter ((tapeWidth doc >=) . I.maxWidth) ds)

render :: Monoid ann => Doc cfg ann -> [[(ann, String)]]
render (Doc []) = []
render (Doc ds) = I.render $ minimumBy (compare `on` I.height) ds

fail :: Doc cfg ann
fail = Doc []

-- Should we fail or not for literals that are too big?
text :: (HasCallStack, DocConfig cfg, Monoid ann) => String -> Doc cfg ann
text str = case cutOff (fromString str) of
  Doc [] -> error ("String too long :" ++ show str)
  doc -> doc

instance (DocConfig cfg, Monoid ann) => Semigroup (Doc cfg ann) where
  Doc bs1 <> Doc bs2 = cutOff $ Doc ((<>) <$> bs1 <*> bs2)

empty :: Monoid ann => Doc cfg ann
empty = Doc [I.text ""]

annotate :: Semigroup ann => ann -> Doc cfg ann -> Doc cfg ann
annotate ann (Doc ds) = Doc (I.annotate ann <$> ds)

indent :: (DocConfig cfg, Monoid ann) => Int -> Doc cfg ann -> Doc cfg ann
indent n d = spaces n <> d

instance (DocConfig cfg, Monoid ann) => Monoid (Doc cfg ann) where
  mempty = empty

(<+>) :: (DocConfig cfg, Monoid ann) => Doc cfg ann -> Doc cfg ann -> Doc cfg ann
d <+> e = d <> space <> e

char :: Monoid ann => Char -> Doc cfg ann
char c = Doc [I.text [c]]

spaces :: Monoid ann => Int -> Doc cfg ann
spaces i = Doc [I.text (replicate i ' ')]

semi, colon, comma, space, dot :: Monoid ann => Doc cfg ann

semi = char ';'
colon = char ':'
comma = char ','
space = char ' '
dot = char '.'

backslash, forwardslash, equal :: Monoid ann => Doc cfg ann

backslash = char '\\'
forwardslash = char '/'
equal = char '='

squote, dquote :: Monoid ann => Doc cfg ann

squote = char '\''
dquote = char '"'

lparen, rparen, langle, rangle, lbrace, rbrace, lbracket, rbracket :: Monoid ann => Doc cfg ann

lparen = char '('
rparen = char ')'
langle = char '<'
rangle = char '>'
lbrace = char '{'
rbrace = char '}'
lbracket = char '['
rbracket = char ']'

flush :: Doc cfg ann -> Doc cfg ann
flush (Doc ds) = Doc (I.flush <$> ds)

($$) :: (DocConfig cfg, Monoid ann) => Doc cfg ann -> Doc cfg ann -> Doc cfg ann
d $$ e = flush d <> e

alts :: [Doc cfg ann] -> Doc cfg ann
alts ds = Doc (concatMap runDoc ds)

foldDoc :: Monoid ann => (Doc cfg ann -> Doc cfg ann -> Doc cfg ann) -> [Doc cfg ann] -> Doc cfg ann
foldDoc c [] = empty
foldDoc c [x] = x
foldDoc c (x : xs) = c x (foldDoc c xs)

hsep :: (DocConfig cfg, Monoid ann) => [Doc cfg ann] -> Doc cfg ann
hsep = foldDoc (<+>)

hsepBy :: (DocConfig cfg, Monoid ann) => Doc cfg ann -> [Doc cfg ann] -> Doc cfg ann
hsepBy s = foldDoc (\x y -> x <> s <+> y)

vcat :: (DocConfig cfg, Monoid ann) => [Doc cfg ann] -> Doc cfg ann
vcat = foldDoc ($$)

sep :: (DocConfig cfg, Monoid ann) => [Doc cfg ann] -> Doc cfg ann
sep [] = empty
sep ds = alts [hsep ds, vcat ds]

between :: (DocConfig cfg, Monoid ann) => Doc cfg ann -> Doc cfg ann -> Doc cfg ann -> Doc cfg ann
between d f e = d <> e <> f

parens :: (DocConfig cfg, Monoid ann) => Doc cfg ann -> Doc cfg ann
parens = between lparen rparen

parenthesise :: (DocConfig cfg, Monoid ann) => Bool -> Doc cfg ann -> Doc cfg ann
parenthesise b = if b then parens else id

newline :: Monoid ann => Doc cfg ann
newline = flush empty

softline :: Monoid ann => Doc cfg ann
softline = alts [space, newline]

matrix :: Monoid ann => (a -> Doc () ann) -> [[a]] -> Doc () ann
matrix cell
  = indent 2
  . vcat
  . ((text "i\\j" <+> foldDoc (\x y -> x <> indent 2 y) (map (text . show) [0..7])) :)
  . zipWith (\ x y -> x <> indent 2 y) (map (text . show) [0..])
  . map
        ( between lbracket rbracket
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

test :: Monoid ann => (Doc () ann -> String) -> Doc () ann -> Doc () ann -> IO ()
test format one zero
  = putStr
  $ format
  $ matrix (\ b -> if b then one else zero) testMatrix

testU = test (unlines . map (concatMap snd) . render) (char '1' :: Doc () ()) (char '0')
