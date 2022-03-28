module Doc.Render.Terminal where

import Control.Applicative
import Data.List
import Data.Maybe

import Doc (Config(..), initConfig, Doc, test, char)
import qualified Doc
import ANSI (Annotation(..), Layer(..), Colour(..), Weight(..), Underlining(..))
import qualified ANSI

data Annotations = Annotations
  { foregroundColour :: Maybe Colour
  , backgroundColour :: Maybe Colour
  , fontWeight       :: Maybe Weight
  , fontUnderlining  :: Maybe Underlining
  } deriving (Show)

instance Semigroup Annotations where
  Annotations fg1 bg1 fw1 fu1 <> Annotations fg2 bg2 fw2 fu2
    = Annotations (fg2 <|> fg1) (bg2 <|> bg1) (fw2 <|> fw1) (fu2 <|> fu1)

instance Monoid Annotations where
  mempty = Annotations Nothing Nothing Nothing Nothing

toANSIs :: Annotations -> [Annotation]
toANSIs (Annotations fg bg fw fu)
    = catMaybes
    [ SetColour Foreground <$> fg
    , SetColour Background <$> bg
    , SetWeight <$> fw
    , SetUnderlining <$> fu
    ]

fromANSIs :: [Annotation] -> Annotations
fromANSIs = foldl (\ acc ann -> acc <> fromANSI ann) mempty where
  fromANSI :: Annotation -> Annotations
  fromANSI (SetColour Foreground c) = mempty { foregroundColour = Just c }
  fromANSI (SetColour Background c) = mempty { backgroundColour = Just c }
  fromANSI (SetWeight w) = mempty { fontWeight = Just w }
  fromANSI (SetUnderlining u) = mempty { fontUnderlining = Just u }

render :: Config -> Doc Annotations -> String
render cfg d
  = intercalate "\n"
  $ map (concatMap (uncurry (ANSI.withANSI . toANSIs)))
  $ Doc.render cfg d

withANSI :: [Annotation] -> Doc Annotations -> Doc Annotations
withANSI = Doc.annotate . fromANSIs

testT = test (render (initConfig { tapeWidth = 80 }) . withANSI [ SetColour Background Blue ])
  (fancyChar Green '1')
  (fancyChar Red '0')

  where fancyChar col c
          = withANSI [ SetColour Foreground col
                     , SetColour Background Magenta
                     , SetWeight Bold
                     ] (char c)
