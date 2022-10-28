{-|
Description: Annotations that can be put on text to be printed
-}
module Doc.Annotations where

import Control.Applicative ((<|>))

import ANSI (Annotation(..),Colour,Weight,Underlining,Layer(..))
import Text.PrettyPrint.Compact (Doc, annotate)
import Data.Maybe (catMaybes)

-- | The 'Annotations' that we can choose to put on text.
data Annotations = Annotations
  { foregroundColour :: Maybe Colour
  , backgroundColour :: Maybe Colour
  , fontWeight       :: Maybe Weight
  , fontUnderlining  :: Maybe Underlining
  } deriving (Eq, Show)

-- | Inherit the 'Semigroup' instance pointwise
instance Semigroup Annotations where
  Annotations fg1 bg1 fw1 fu1 <> Annotations fg2 bg2 fw2 fu2
    = Annotations (fg2 <|> fg1) (bg2 <|> bg1) (fw2 <|> fw1) (fu2 <|> fu1)

-- | Inherit the 'Monoid' instance pointwise
instance Monoid Annotations where
  mempty = Annotations Nothing Nothing Nothing Nothing

-- | Break up an Annotations as a record into a list of its constituent commands
toANSIs :: Annotations -> [Annotation]
toANSIs (Annotations fg bg fw fu)
    = catMaybes
    [ SetColour Foreground <$> fg
    , SetColour Background <$> bg
    , SetWeight <$> fw
    , SetUnderlining <$> fu
    ]

-- | Create a single annotation record from a list of annotations
fromANSIs :: [Annotation] -> Annotations
fromANSIs = foldl (\ acc ann -> acc <> fromANSI ann) mempty where
  fromANSI :: Annotation -> Annotations
  fromANSI (SetColour Foreground c) = mempty { foregroundColour = Just c }
  fromANSI (SetColour Background c) = mempty { backgroundColour = Just c }
  fromANSI (SetWeight w) = mempty { fontWeight = Just w }
  fromANSI (SetUnderlining u) = mempty { fontUnderlining = Just u }

-- | Add some annotations to some 'Doc'
withANSI :: [Annotation] -> Doc Annotations -> Doc Annotations
withANSI = annotate . fromANSIs
