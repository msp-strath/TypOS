module Term.Mangler where

import Control.Monad.Writer
import Control.Applicative
import qualified Data.Map as Map

import Thin
import Hide
import Term.Base
import Term.Substitution

data Mangler f {-xi-} {-ga-} = Mangler
  { mangGlo :: Int -- size of xi
  , mangLoc :: Int -- size of ga
  , mangV :: f (Term {-xi <<< ga -}) -- ga is singleton
  , mangB :: Mangler f {-xi-} {-ga , x-}        -- how to mangle under a relevant binder
  , mangM :: Meta {-de-} -> f (Subst {-xi <<< de --> xi <<< ga -}) -> f (Term {-xi <<< ga -})
  , mangSelFrom :: Th {-ga0 <= ga -}
                -> Mangler f {-xi-} {-ga0-}
  }

mangTgt :: Mangler f -> Int
mangTgt mu = mangGlo mu + mangLoc mu

mangW :: Mangler f {-xi-} {-ga0 <<< ga1-} ->
         Int ->  -- size of ga1
         Mangler f {-xi-} {-ga0-}
mangW mu w = mangSelFrom mu (ones (mangLoc mu - w) <> none w)

stanMangler :: Int -- number of global vars xi
            -> Int -- number of local vars ga
            -> Map.Map Meta (Term {-xi <<< de-}) -- de are vars in pattern you are allowed to depend on
            -> Mangler (Writer Any) {-xi-} {-ga-}
stanMangler xi ga tbl = Mangler
  { mangGlo = xi
  , mangLoc = ga
  , mangV = pure (CdB V (none xi -? True))
  , mangB = stanMangler xi (ga + 1) tbl
  , mangM = \ m sg ->
      case Map.lookup m tbl of
        Nothing -> (m $:) <$> sg
        Just t -> (t //^) <$> sg <* tell (Any True)
  , mangSelFrom = \ ph -> stanMangler xi (weeEnd ph) tbl
  }

depMangler :: Foldable t => t Meta -- do we depend on any of these metas?
            -> Mangler (Const Any)
depMangler ms = Mangler
  { mangGlo = 0 -- hack
  , mangLoc = 0 -- hack
  , mangV = Const mempty
  , mangB = depMangler ms
  , mangM = \ m sg -> sg *> (Const $ Any $ m `elem` ms)
  , mangSelFrom = \ ph -> depMangler ms
  }


class Manglable t where
  mangle  :: Applicative f => Mangler f {-xi-} {-ga-} -> t {-ga-} -> f (CdB t {- xi <<< ga-})
  -- -- mangle' is worker for mangle
  -- mangle' :: Applicative f => Mangler m m' f -> t m -> f (CdB (t m'))
  mangleCdB :: Applicative f => Mangler f {-xi-} {-ga-} -> CdB (t {-ga-}) -> f (CdB (t {- xi <<< ga-}))

  {-
  mangle mu t = case mangTh mu of
    Just th -> pure (t, th)
    Nothing -> mangle' mu t
  -}

  mangleCdB mu (CdB t th) = mangle mu' t where
    -- we recheck for mangI after doing a selection computing m'
    mu' = mangSelFrom mu th

instance Manglable a => Manglable (Named a) where
  mangle mu (x := a) = ((x :=) $^) <$> mangle mu a

instance Manglable (Tm Meta) where
  mangle mu V = mangV mu
  mangle mu (A a) = pure (atom a (mangTgt mu))
  mangle mu (P k p) = (P k $^) <$> mangle mu p
  mangle mu ((Hide x := False) :. t) = (x \\) <$> (weak <$> mangle mu t)
  mangle mu ((Hide x := True) :. t) = (x \\) <$> mangle (mangB mu) t
  mangle mu (m :$ sg) = mangM mu m (mangle mu sg)

instance (Manglable a, Manglable b) => Manglable (RP a b) where
  mangle mu (a :<>: b)  = (<&>) <$> mangleCdB mu a <*> mangleCdB mu b

instance Manglable (Sbst Meta) where
  mangle mu (sg :^^ w) = sbstW <$> sg' <*> pure (ones w) where
    mu' = mangW mu w
    sg' = case sg of
      S0 -> pure (sbstI (mangGlo mu))
      ST (sg :<>: t) -> sbstT <$> mangleCdB mu' sg <*> mangleCdB mu' t
