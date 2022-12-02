module Info where
import Control.Monad

-- Partial info

data Info a = Unknown | Known a | Inconsistent
  deriving (Show, Eq, Functor)


instance Applicative Info where
  pure = Known
  (<*>) = ap

instance Monad Info where
  Unknown >>= f = Unknown
  Known a >>= f = f a
  Inconsistent >>= f = Inconsistent

instance Eq a => Semigroup (Info a) where
  Unknown <> y = y
  x <> Unknown = x
  Known x <> Known y | x == y = Known x
  _ <> _ = Inconsistent

instance Eq a => Monoid (Info a) where
  mempty = Unknown
