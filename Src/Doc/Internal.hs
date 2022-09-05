-- Module based on Jean-Philippe Bernardy's functional pearl
-- "A Pretty But Not Greedy Printer"
-- (or rather my Agda port of it in the stdlib's Text.Pretty)

module Doc.Internal where

import Data.Bifunctor
import GHC.Stack
import Bwd

data Tree ann a
  = Leaf
  | Indent !Int (Tree ann a)
  | Node (Tree ann a) a (Tree ann a)
  | Annotate ann (Tree ann a)
  deriving (Show, Functor)

-- auxiliary function used to fuse blocks
node :: Maybe (a, Tree ann a) -> a -> Tree ann a -> Maybe (a, Tree ann a)
node Nothing y ys = Just (y, ys)
node (Just (x, xs)) y ys = Just (x, Node xs y ys)

-- auxiliary function
treeIndent :: Int -> Tree ann a -> Tree ann a
treeIndent 0 t = t
treeIndent m Leaf = Leaf
treeIndent m (Indent n t) = Indent (m + n) t
treeIndent m (Annotate ann t) = Annotate ann (treeIndent m t)
treeIndent m t = Indent m t

treeAnnotate :: Semigroup ann => ann -> Tree ann a -> Tree ann a
treeAnnotate ann Leaf = Leaf
treeAnnotate ann (Indent m t) = Indent m (treeAnnotate ann t)
treeAnnotate ann (Annotate ann' t) = Annotate (ann <> ann') t
treeAnnotate ann t = Annotate ann t

data Span ann
  = Literal !ann !String
  | Indents !Int
  deriving (Show, Functor)

newtype Line ann = Line { runLine :: Bwd (Span ann) }
  deriving (Show, Functor)

instance Eq ann => Semigroup (Line ann) where
{-
  -- not sure which implementation to pick

  -- 1. append & then group
  Line lz <> Line rz = Line
    $ fmap (\ xxs -> (fst (top xxs), foldMap snd xxs))
    $ Bwd.groupBy ((==) `on` fst) (lz <> rz)
-}

  -- 2. alternatively, assuming both sides are already fused
  Line B0 <> Line rz = Line rz
  Line lz <> Line B0 = Line lz
  Line llz@(lz :< Literal al l) <> Line rz = Line $
    case rz <>> [] of
      (Literal ar r):rs | al == ar -> lz :< Literal al (l <> r) <>< rs
      _ -> llz <> rz
  Line lz <> Line rz = Line (lz <> rz)

instance Eq ann => Monoid (Line ann) where
  mempty = Line B0

asLine :: (Eq ann, Monoid ann) => String -> Line ann
asLine "" = mempty
asLine str = Line (singleton $ Literal mempty str)

-- A block has the shape
-- ```
--    first line
--    rest of the block
--    ...
--    last line
-- ```
-- so that we can conveniently concat two blocks by putting together
-- 1. the last line of the first block
-- 2. the first line of the second block
data Block ann = Block
  { height    :: !Int                                  -- height of the block
  , chunk     :: Maybe (Line ann, Tree ann (Line ann)) -- of size height
  , maxWidth  :: !Int
  , lastWidth :: !Int
  , lastLine  :: Line ann
  } deriving (Show)

instance Eq (Block ann) where
  Block h1 _ mw1 lw1 _ == Block h2 _ mw2 lw2 _
    = h1 == h2 && mw1 == mw2 && lw1 == lw2

instance Ord (Block ann) where
  Block h1 _ mw1 lw1 _ < Block h2 _ mw2 lw2 _
    = h1 <= h2 && mw1 <= mw2 && lw1 <= lw2
  b1 <= b2 = b1 == b2 || b1 < b2

instance Functor Block where
  fmap f (Block h c mw lw l) = Block h (bimap (f <$>) (mapTree f) <$> c) mw lw (f <$> l)

    where

      mapTree f Leaf = Leaf
      mapTree f (Indent m t) = Indent m (mapTree f t)
      mapTree f (Annotate ann t) = Annotate (f ann) (mapTree f t)
      mapTree f (Node l m r) = Node (mapTree f l) (f <$> m) (mapTree f r)

annotate :: Semigroup ann => ann -> Block ann -> Block ann
annotate ann (Block h c mw lw l)
  = Block h (bimap ((ann <>) <$>) (treeAnnotate ann) <$> c) mw lw ((ann <>) <$> l)

indent :: Int -> Block ann
indent i = Block
  { height    = 0
  , chunk     = Nothing
  , maxWidth  = i
  , lastWidth = i
  , lastLine  = Line (B0 :< Indents i)
  }

-- A text is assumed not to contain any newline character
text :: (HasCallStack, Eq ann, Monoid ann) => String -> Block ann
text str | any (`elem` "\n\r") str = error ("Invalid text: " ++ show str)
text str = let n = length str in Block
  { height    = 0
  , chunk     = Nothing
  , maxWidth  = n
  , lastWidth = n
  , lastLine  = asLine str
  }

spaces :: (Eq ann, Monoid ann) => Int -> Block ann
spaces i = text (replicate i ' ')

-- We can't "unlines lines" because that would introduce extra newlines
para :: (HasCallStack, Eq ann, Monoid ann) => String -> Block ann
para = go mempty where

  go acc str = case span ('\n' /=) str of
    (str, []) -> acc <> text str
    (str, _:rest) -> go (flush (acc <> text str)) rest

instance (Eq ann, Monoid ann) => Semigroup (Block ann) where
  Block h1 c1 mw1 lw1 l1 <> Block h2 c2 mw2 lw2 l2 = Block
    { height    = h1 + h2
    , chunk     = c12
    , maxWidth  = max mw1 (lw1 + mw2)
    , lastWidth = lw1 + lw2
    , lastLine  = l12
    }

    where
      (c12, l12) =
        case c2 of
          Nothing -> (c1, l1 <> l2)
          Just (f2, b2) -> ( node c1 (l1 <> f2) (treeIndent lw1 b2)
                           , if lw1 == 0 then l2 else Line (B0 :< Indents lw1) <> l2)

instance (Eq ann, Monoid ann) => Monoid (Block ann) where
  mempty = text ""

-- introduce a new line at the end
flush :: Eq ann => Block ann -> Block ann
flush (Block h c mw lw l) = Block (1+h) (node c l Leaf) mw 0 mempty

foldBlock :: (Eq ann, Monoid ann) => (Block ann -> Block ann -> Block ann) ->
           [Block ann] -> Block ann
foldBlock c [] = mempty
foldBlock c [x] = x
foldBlock c (x : xs) = c x (foldBlock c xs)

render :: forall ann. Monoid ann => Block ann -> [[(ann, String)]]
render b = (<>> []) $ go B0 mempty ""
         $ maybe Leaf (uncurry (Node Leaf))
         $ node (chunk b) (lastLine b) Leaf

  where

  goLine :: [(ann, String)] -> ann -> Bwd (Span ann) -> [(ann, String)]
  goLine acc ann B0 = acc
  goLine acc ann (spz :< sp) = case sp of
    Literal ann' str -> goLine ((ann <> ann', str) : acc) ann spz
    Indents n -> goLine ((mempty, replicate n ' ') : acc) ann spz

  go :: Bwd [(ann, String)] -> ann -> String -> Tree ann (Line ann) -> Bwd [(ann, String)]
  go acc ann ind Leaf = acc
  go acc ann ind (Annotate ann' t) = go acc (ann <> ann') ind t
  go acc ann ind (Indent m t) = go acc ann (replicate m ' ' ++ ind) t
  go acc ann ind (Node xs l ys)
    = let l' = (mempty, ind) : (goLine [] ann $ runLine l) in
      go (go acc ann ind xs :< l') ann ind ys
