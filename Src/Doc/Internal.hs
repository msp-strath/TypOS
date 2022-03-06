-- Module based on Jean-Philippe Bernardy's functional pearl
-- "A Pretty But Not Greedy Printer"
-- (or rather my Agda port of it in the stdlib's Text.Pretty)

module Doc.Internal where

import GHC.Stack
import Bwd

data Tree a
  = Leaf
  | Indent !Int (Tree a)
  | Node (Tree a) !a (Tree a)
  deriving (Functor)

-- auxiliary function used to fuse blocks
node :: Maybe (a, Tree a) -> a -> Tree a -> Maybe (a, Tree a)
node Nothing y ys = Just (y, ys)
node (Just (x, xs)) y ys = Just (x, Node xs y ys)

-- auxiliary function
indent :: Int -> Tree a -> Tree a
indent 0 t = t
indent m (Indent n t) = Indent (m + n) t
indent m t = Indent m t

-- A block as the shape
-- ```
--    first line
--    rest of the block
--    ...
--    last line
-- ```
-- so that we can conveniently concat two blocks by putting together
-- 1. the last line of the first block
-- 2. the first line of the second block
data Block = Block
  { height    :: !Int                          -- height of the block
  , chunk     :: (Maybe (String, Tree String)) -- of size height
  , maxWidth  :: !Int
  , lastWidth :: !Int
  , lastLine  :: String
  }

-- A text is assumed not to contain any newline character
text :: HasCallStack => String -> Block
text str | any (`elem` "\n\r") str = error ("Invalid text: " ++ show str)
text str = let n = length str in Block
  { height    = 0
  , chunk     = Nothing
  , maxWidth  = n
  , lastWidth = n
  , lastLine  = str
  }

instance Semigroup Block where
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
          Nothing -> (c1, l1 ++ l2)
          Just (f2, b2) -> ( node c1 (l1 ++ f2) (indent lw1 b2)
                           , replicate lw1 ' ' ++ l2)

instance Monoid Block where
  mempty = text ""

-- introduce a new line at the end
flush :: Block -> Block
flush (Block h c mw lw l) = Block (1+h) (node c l Leaf) mw 0 ""

render :: Block -> String
render b = unlines $ (<>> []) $ go B0 ""
         $ maybe Leaf (uncurry (Node Leaf))
         $ node (chunk b) (lastLine b) Leaf

  where

  go :: Bwd String -> String -> Tree String -> Bwd String
  go acc ind Leaf = acc
  go acc ind (Indent m t) = go acc (replicate m ' ' ++ ind) t
  go acc ind (Node xs str ys) = go (go acc ind xs :< ind ++ str) ind ys
