{-# LANGUAGE ScopedTypeVariables #-}

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

newtype Line ann = Line { runLine :: Bwd (ann, String) }
  deriving (Show, Semigroup, Monoid, Functor)

asLine :: Monoid ann => String -> Line ann
asLine "" = mempty
asLine str = Line (singleton (mempty, str))

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

-- A text is assumed not to contain any newline character
text :: (HasCallStack, Monoid ann) => String -> Block ann
text str | any (`elem` "\n\r") str = error ("Invalid text: " ++ show str)
text str = let n = length str in Block
  { height    = 0
  , chunk     = Nothing
  , maxWidth  = n
  , lastWidth = n
  , lastLine  = asLine str
  }

instance Monoid ann => Semigroup (Block ann) where
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
                           , if lw1 == 0 then l2 else asLine (replicate lw1 ' ') <> l2)

instance Monoid ann => Monoid (Block ann) where
  mempty = text ""

-- introduce a new line at the end
flush :: Block ann -> Block ann
flush (Block h c mw lw l) = Block (1+h) (node c l Leaf) mw 0 mempty

render :: forall ann. Monoid ann => Block ann -> [[(ann, String)]]
render b = (<>> []) $ go B0 mempty ""
         $ maybe Leaf (uncurry (Node Leaf))
         $ node (chunk b) (lastLine b) Leaf

  where

  go :: Bwd [(ann, String)] -> ann -> String -> Tree ann (Line ann) -> Bwd [(ann, String)]
  go acc ann ind Leaf = acc
  go acc ann ind (Annotate ann' t) = go acc (ann <> ann') ind t
  go acc ann ind (Indent m t) = go acc ann (replicate m ' ' ++ ind) t
  go acc ann ind (Node xs l ys)
    = let l' = (ann, ind) : (runLine ((ann <>) <$> l) <>> []) in
      go (go acc ann ind xs :< l') ann ind ys
