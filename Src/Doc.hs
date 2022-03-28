{-# LANGUAGE OverloadedStrings #-}

-- Module based on Jean-Philippe Bernardy's functional pearl
-- "A Pretty But Not Greedy Printer"
-- (or rather my Agda port of it in the stdlib's Text.Pretty)

module Doc where

import Data.Function
import Data.List
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as L1
import Data.String
import GHC.Stack

import Doc.Internal (Block)
import qualified Doc.Internal as I

data Orientation = Vertical | Horizontal

data Config = Config
  { tapeWidth   :: Int
  , orientation :: Orientation
  }

initConfig :: Int -> Config
initConfig i = Config i Horizontal

-- | A document is a computation that, given a tape width,
--   will return a non-empty list of candidates.
--   We try to force the result to fit in the tape width's
--   but if no solution would do, we'll ignore the constraint
--   to guarantee we get a result back.
newtype Doc ann = Doc { runDoc :: Config -> NonEmpty (Block ann) }

instance Functor Doc where
  fmap f (Doc ds) = Doc (L1.map (f <$>) . ds)

instance Monoid ann => IsString (Doc ann) where
  fromString str = Doc (const (I.para str :| []))

-- | cutOff will filter the potential results based on the
--   tape width.
cutOff :: Doc ann -> Doc ann
cutOff doc@(Doc ds) = Doc $ \ cfg -> let i = tapeWidth cfg in
  let candidates = ds cfg in
  case L1.filter ((i >=) . I.maxWidth) candidates of
    -- none of them are good enough so we may as well already commit to
    -- the most compact representation
    [] -> minimumBy (compare `on` I.height) (L1.toList candidates) :| []
    -- Otherwise we're happy to proceed with the compact enough outputs
    d:ds -> d :| ds

render :: Monoid ann => Config -> Doc ann -> [[(ann, String)]]
render cfg (Doc ds)
  = I.render
  $ minimumBy (compare `on` I.height)
  $ L1.toList (ds cfg)

instance Show (Doc ann) where
  show = unlines . map (concatMap snd) . render initConfig . (() <$)

-- Should we fail or not for literals that are too big?
text :: Monoid ann => String -> Doc ann
text str = fromString str

instance Monoid ann => Semigroup (Doc ann) where
  Doc bs1 <> Doc bs2 = cutOff $ Doc (\ i -> (<>) <$> bs1 i <*> bs2 i)

empty :: Monoid ann => Doc ann
empty = fromString ""

annotate :: Semigroup ann => ann -> Doc ann -> Doc ann
annotate ann (Doc ds) = Doc (\ i -> I.annotate ann <$> ds i)

indent :: Monoid ann => Int -> Doc ann -> Doc ann
indent n d = spaces n <> d

instance Monoid ann => Monoid (Doc ann) where
  mempty = empty

(<+>) :: Monoid ann => Doc ann -> Doc ann -> Doc ann
d <+> e = d <> space <> e

char :: Monoid ann => Char -> Doc ann
char c = fromString [c]

spaces :: Monoid ann => Int -> Doc ann
spaces i = fromString (replicate i ' ')

semi, colon, comma, space, dot :: Monoid ann => Doc ann

semi = char ';'
colon = char ':'
comma = char ','
space = char ' '
dot = char '.'

backslash, forwardslash, equal, pipe :: Monoid ann => Doc ann

backslash = char '\\'
forwardslash = char '/'
equal = char '='
pipe = char '|'

squote, dquote :: Monoid ann => Doc ann

squote = char '\''
dquote = char '"'

lparen, rparen, langle, rangle, lbrace, rbrace, lbracket, rbracket :: Monoid ann => Doc ann

lparen = char '('
rparen = char ')'
langle = char '<'
rangle = char '>'
lbrace = char '{'
rbrace = char '}'
lbracket = char '['
rbracket = char ']'

flush :: Doc ann -> Doc ann
flush (Doc ds) = Doc ((I.flush <$>) <$> ds)

($$) :: Monoid ann => Doc ann -> Doc ann -> Doc ann
d $$ e = flush d <> e

alts :: HasCallStack => [Doc ann] -> Doc ann
alts [] = error "Using alts with an empty list"
alts (d:ds) = cutOff $ Doc (go d ds) where

  go :: Doc ann -> [Doc ann] -> Config -> NonEmpty (Block ann)
  go d [] i = runDoc d i
  go d (e:es) i = runDoc d i <> go e es i

foldDoc :: Monoid ann => (Doc ann -> Doc ann -> Doc ann) ->
           [Doc ann] -> Doc ann
foldDoc c [] = empty
foldDoc c [x] = x
foldDoc c (x : xs) = c x (foldDoc c xs)

hsep :: Monoid ann => [Doc ann] -> Doc ann
hsep = foldDoc (<+>)

hsepBy :: Monoid ann => Doc ann -> [Doc ann] -> Doc ann
hsepBy s = foldDoc (\x y -> x <> s <+> y)

vcat :: Monoid ann => [Doc ann] -> Doc ann
vcat = foldDoc ($$)

sep :: Monoid ann => [Doc ann] -> Doc ann
sep [] = empty
sep ds = alts [hsep ds, vcat ds]

between :: Monoid ann => Doc ann -> Doc ann -> Doc ann -> Doc ann
between d f e = d <> e <> f

parens :: Monoid ann => Doc ann -> Doc ann
parens = between lparen rparen

parenthesise :: Monoid ann =>
                Bool -> Doc ann -> Doc ann
parenthesise b = if b then parens else id

brackets :: Monoid ann => Doc ann -> Doc ann
brackets = between lbracket rbracket

braces :: Monoid ann => Doc ann -> Doc ann
braces = between lbrace rbrace

matrix :: Monoid ann => (a -> Doc ann) -> [[a]] -> Doc ann
matrix cell
  = indent 2
  . vcat
  . ((text "i\\j" <+> foldDoc (\x y -> x <> indent 2 y) (map (text . show) [0..7])) <> space :)
  . zipWith (\ x y -> x <> indent 2 y) (map (text . show) [0..])
  . map
        ( between lbracket rbracket
        . hsepBy comma
        . map cell
        )

testMatrix :: [[Bool]]
testMatrix = do
  i <- [1..10]
  pure $ do
    j <- [1..8]
    pure (j `mod` i /= 0)

test :: Monoid ann => (Doc ann -> String) -> Doc ann -> Doc ann -> IO ()
test format one zero
  = putStr
  $ format
  $ matrix (\ b -> if b then one else zero) testMatrix

testU = test (unlines . map (concatMap snd) . render (initConfig { tapeWidth = 80 }))
        (char '1' :: Doc ())
        (char '0')
