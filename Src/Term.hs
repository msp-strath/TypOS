{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE
  DeriveTraversable,
  FlexibleInstances,
  TypeSynonymInstances,
  LambdaCase,
  TupleSections,
  MultiParamTypeClasses
  #-}

module Term where

import Data.Maybe (fromMaybe)
import Control.Monad.Writer
import Control.Applicative
import Data.Traversable
import qualified Data.Map as Map

import Bwd
import Thin
import Hide

-- import Debug.Trace

track = const id
-- track = trace

data Tm m
  = V
  | A String
  | P (RP (Tm m) (Tm m))
  | Named Bool :. Tm m
  | m :$ Sbst m
  deriving (Show, Eq, Ord)

data Named a = Hide String := a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Traversable Tm where
  traverse f V = pure V
  traverse f (A a) = pure (A a)
  traverse f (P ((s, th) :<>: (t, ph))) =
     P <$> ((:<>:) <$> ((, th) <$> traverse f s) <*> ((, ph) <$> traverse f t))
  traverse f (xb :. t) = (xb :.) <$> traverse f t
  traverse f (m :$ (sg :^^ w)) =
    (:$) <$> f m <*> ((:^^ w) <$> traverse f sg)
instance Functor Tm where fmap = fmapDefault
instance Foldable Tm where foldMap = foldMapDefault

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
  , mangV = pure (V, none xi -? True)
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

  mangleCdB mu (t, th) = mangle mu' t where
    -- we recheck for mangI after doing a selection computing m'
    mu' = mangSelFrom mu th

instance Manglable a => Manglable (Named a) where
  mangle mu (x := a) = ((x :=) $^) <$> mangle mu a

instance Manglable (Tm Meta) where
  mangle mu V = mangV mu
  mangle mu (A a) = pure (atom a (mangTgt mu))
  mangle mu (P p) = (P $^) <$> mangle mu p
  mangle mu ((Hide x := False) :. t) = (x \\) <$> (weak <$> mangle mu t)
  mangle mu ((Hide x := True) :. t) = (x \\) <$> mangle (mangB mu) t
  mangle mu (m :$ sg) = mangM mu m (mangle mu sg)

instance (Manglable a, Manglable b) => Manglable (RP a b) where
  mangle mu (a :<>: b)  = (<&>) <$> mangleCdB mu a <*> mangleCdB mu b

newtype Meta = Meta [(String, Int)]
  deriving (Show, Ord, Eq)
type Term = CdB (Tm Meta)
type Subst = CdB (Sbst Meta)
type Root = ( Bwd (String, Int) -- name prefix
            , Int)              -- counter

initRoot :: Root
initRoot = (B0, 0)

-- fresh meta in the current root space
meta :: Root -> String -> (Meta, Root)
meta (xiz, j) x = (Meta (xiz <>> [(x, j)]), (xiz, j + 1))

splitRoot :: Root -> String -> (Root, Root)
splitRoot (xiz, j) x = ((xiz :< (x, j), 0), (xiz, j + 1))

infixr 3 :.
infixr 5 :$

-- relevant substitutions
data Sbst m = (:^^)
  (Sbst' m)  -- what's below the weakenings
  Int      -- how many weakenings
  deriving (Show, Eq, Ord)

data Sbst' m
  = S0 -- empty -> empty
  | ST (RP (Sbst m) (Named (Tm m)))
  deriving (Show, Eq, Ord)

instance Traversable Sbst where
  traverse f (sg :^^ w) = (:^^ w) <$> traverse f sg
instance Functor Sbst where fmap = fmapDefault
instance Foldable Sbst where foldMap = foldMapDefault

instance Traversable Sbst' where
  traverse f S0 = pure S0
  traverse f (ST ((sg, th) :<>: (t, ph))) = ST <$>
    ((:<>:) <$> ((, th) <$> traverse f sg)
            <*> ((, ph) <$> traverse (traverse f) t))
instance Functor Sbst' where fmap = fmapDefault
instance Foldable Sbst' where foldMap = foldMapDefault

instance Manglable (Sbst Meta) where
  mangle mu (sg :^^ w) = sbstW <$> sg' <*> pure (ones w) where
    mu' = mangW mu w
    sg' = case sg of
      S0 -> pure (sbstI (mangGlo mu))
      ST (sg :<>: t) -> sbstT <$> mangleCdB mu' sg <*> mangleCdB mu' t


-- smart constructors
sbst0 :: Int -> CdB (Sbst m)
sbst0 de = ((S0 :^^ 0), none de)

sbstW :: CdB (Sbst m) -> Th -> CdB (Sbst m)
sbstW ((sg :^^ w), th) ph = ((sg :^^ (w + weeEnd ph)), th <> ph)

sbstT :: CdB (Sbst m) -> CdB (Named (Tm m)) -> CdB (Sbst m)
sbstT sg t = ((ST p :^^ 0), ps) where (p, ps) = sg <&> t

sbstI :: Int -> CdB (Sbst m)
sbstI w = ((S0 :^^ w), ones w)

topSbst :: String -> CdB (Tm m) -> CdB (Sbst m)
topSbst x t = sbstT (sbstI (scope t)) ((Hide x :=) $^ t)

sbstCod :: Sbst m -> Int
sbstCod (sg :^^ w) = case sg of
  S0 -> w
  ST ((sg, th) :<>: (t, ph)) -> bigEnd th + w

sbstDom :: Sbst m -> Int
sbstDom (sg :^^ w) = case sg of
 S0 -> w
 ST ((sg, th) :<>: (t, ph)) -> sbstDom sg + 1 + w

sbstSel
  :: Th -- ga0 from ga
  -> Sbst m -- ga -> de
  -> CdB (Sbst m)
sbstSel th (S0 :^^ w) = ((S0 :^^ weeEnd th), th) -- w = bigEnd th
sbstSel th (ST ((sg, phl{- del <= de -}) :<>: t) :^^ w) =
  sbstW (if b then sbstT sg0 t else sg0) thw
  where
  -- ga, x, w -> de, w
  (thgax, thw) = thChop th w
  (thga, b) = thun thgax
  sg0 = sbstSel thga sg *^ phl

data OrdWit
  = LtBy Int -- positive
  | GeBy Int -- non-negative
  deriving Show

euclid :: Int -> Int -> OrdWit
euclid x y = let d = x - y in case d < 0 of
  True  -> LtBy (negate d)
  False -> GeBy d

(//^) :: Show m => CdB (Tm m) -> CdB (Sbst m) -> CdB (Tm m)
tth@(t, th) //^ sgph@(sg, ph) =
   track "\n" $
   track ("Term: " ++ show tth) $
   track ("Subst: " ++ show sgph) $
   case sbstSel th sg of
     (sg, ps) -> let res = (t // sg, ps <^> ph) in
                 track ("Result: " ++ show res) $
                 track "\n" $
                 res

(//) :: Tm m -> Sbst m -> Tm m
t // (S0 :^^ _) = t
V // (ST (_ :<>: ((_ := t), _)) :^^ 0) = t
P ((tl, thl) :<>: (tr, thr)) // sg =
  P ((tl // sgl, phl) :<>: (tr // sgr, phr)) where
  (sgl, phl) = sbstSel thl sg
  (sgr, phr) = sbstSel thr sg
((x := b) :. t) // (sg :^^ w) = (x := b) :. (t // (sg :^^ if b then w+1 else w))
(m :$ rh) // sg = m :$ (rh /// sg)

(///) :: Sbst m -> Sbst m -> Sbst m
(S0 :^^ _) /// sg = sg
rh /// (S0 :^^ _) = rh
(rh :^^ v) /// (sg :^^ w) =
  case euclid w v of
    LtBy d -> case sg of
      ST ((sg, phl) :<>: t) ->
        (ST (((rh :^^ (d-1)) /// sg, phl) :<>: t) :^^ w)
      {-
          -------  ;  -------
             w           w
          -------     -------
          -------     ----> t
           d > 0         sg
          -------
             rh
      -}
    GeBy d -> case rh of
      ST ((rh, thl) :<>: ((x := s), thr)) -> let
        (sgl, phl) = sbstSel thl (sg :^^ d)
        (sgr, phr) = sbstSel thr (sg :^^ d)
        in (ST ((rh /// sgl, phl) :<>: (x := (s // sgr), phr)) :^^ v)
      {-
        -------  ;  -------
           v           v
        -------     -------
        ----> s     -------
           rh          d
                    -------
                       sg
      -}


-- toplevel expansions and contractions of co-deBruijn terms

data Xn m
  = VX Int Int    -- which free variable out of how many?
  | AX String Int -- how many free variables?
  | CdB (Tm m) :%: CdB (Tm m)
  | String :.: CdB (Tm m)
  | m :$: CdB (Sbst m)
  deriving (Eq, Show{-, Functor, Foldable, Traversable-})

expand :: CdB (Tm m) -> Xn m
expand (t, th) = case t of
  V   -> VX (lsb th) (bigEnd th)
  A a -> AX a (bigEnd th)
  P (s :<>: t) -> (s *^ th) :%: (t *^ th)
  (str := b) :. t -> unhide str :.: (t, th -? b)
  f :$ sg -> f :$: (sg, th)

(?:) :: CdB (Tm m) -> (Xn m -> a) -> a
t ?: f = f (expand t)

contract :: Xn m -> CdB (Tm m)
contract t = case t of
  VX x ga -> (V, inx (x, ga))
  AX a ga -> (A a, none ga)
  s :%: t -> P $^ (s <&> t)
  x :.: (t, th) -> case thun th of
    (th, b) -> ((Hide x := b) :. t, th)
  m :$: sg -> (m :$) $^ sg

-- smart constructors for the codeBruijn terms; bigEnds must agree

var :: Int -> Int -> CdB (Tm m)
var x ga = contract (VX x ga)

atom :: String -> Int -> CdB (Tm m)
atom a ga = contract (AX a ga)

nil :: Int -> CdB (Tm m)
nil = atom ""

infixr 4 %
(%) :: CdB (Tm m) -> CdB (Tm m) -> CdB (Tm m)
s % t = contract (s :%: t)

(#%) :: (String, Int) -> [CdB (Tm m)] -> CdB (Tm m)
(a, ga) #% ts = case foldr (%) (nil ga) ts of
  (t, th) -> (P (atom a ga :<>: (t, ones (weeEnd th))), th)

(#%+) :: String -> [CdB (Tm m)] -> CdB (Tm m)
a #%+ ts = let ga = scope (head ts) in (a, ga) #% ts

class OrBust x where
  bust :: x

instance OrBust (Maybe x) where
  bust = Nothing

instance OrBust Bool where
  bust = False

instance OrBust b => OrBust (a -> b) where
  bust = \ _ -> bust

asTagged :: OrBust x => ((String, Int) -> CdB (Tm m) -> x) -> CdB (Tm m) -> x
asTagged f = asPair $ asAtom f

asAtom :: OrBust x => ((String, Int) -> x) -> CdB (Tm m) -> x
asAtom f t = t ?: \case
 AX s n -> f (s, n)
 _ -> bust

asBind :: OrBust x => (String -> CdB (Tm m) -> x) -> CdB (Tm m) -> x
asBind f t = t ?: \case
 x :.: t -> f x t
 _ -> bust

asPair :: OrBust x => (CdB (Tm m) -> CdB (Tm m) -> x) -> CdB (Tm m) -> x
asPair f t = t ?: \case
  a :%: b -> f a b
  _ -> bust

asNil :: OrBust x => x -> CdB (Tm m) -> x
asNil f = asAtom $ \case
  ("",_) -> f
  _      -> bust

asListOf :: OrBust x => (CdB (Tm m) -> Maybe y) -> ([y] -> x) -> CdB (Tm m) -> x
asListOf asY f = asList $ \ts -> case traverse asY ts of
                                   Just ys -> f ys
                                   Nothing -> bust

asList :: OrBust x => ([CdB (Tm m)] -> x) -> CdB (Tm m) -> x
asList f = asTagged $ \case
  ("Cons",_) -> asPair $ \ a -> asPair $ asList $ \ xs -> asNil $ f (a:xs)
  ("Nil",_) ->  asNil $ f []
  _ -> bust

infixr 3 \\
(\\) :: String -> CdB (Tm m) -> CdB (Tm m)
x \\ t = contract (x :.: t)

infixr 5 $:
($:) :: m -> CdB (Sbst m) -> CdB (Tm m)
m $: sg = contract (m :$: sg)


-- patterns are de Bruijn
data PatF v
  = VP v
  | AP String
  | PP (PatF v) (PatF v)
  | BP (Hide String) (PatF v)
  | MP String Th
  deriving (Show, Functor, Eq)

type Pat = PatF Int

instance Thable v => Thable (PatF v) where
  VP v *^ th = VP (v *^ th)
  AP a *^ th = AP a
  PP p q *^ th = PP (p *^ th) (q *^ th)
  BP x b *^ th = BP x (b *^ (th -? True))
  MP m ph *^ th = MP m (ph *^ th)

(#?) :: String -> [PatF v] -> PatF v
a #? ts = foldr PP (AP "") (AP a : ts)

betaLHS :: Pat
betaLHS = "App" #? [ "Lam" #? [BP (Hide "x") (MP "body" (ones 1))]
                   , MP "arg" (ones 0)
                   ]

betaRHS :: CdB (Tm String)
betaRHS = "body" $: (sbstT (sbst0 0) ((Hide "x" :=) $^ ("arg" $: sbst0 0)))

beta :: Root -> Term -> Maybe (Root, Term)
beta r t = do
  (r, (m, val)) <- match r betaLHS t
  let xi = scope t
  let rhs = fmap (trustMe m) $^ betaRHS
  track (show rhs) $ pure ()
  let (res, _) = runWriter $ mangleCdB (stanMangler xi 0 val) rhs
  pure (r, res)

  where

    trustMe :: Ord a => Map.Map a b -> (a -> b)
    trustMe m v = fromMaybe (error "IMPOSSIBLE") (Map.lookup v m)

redex :: Term
redex = ("App", 2) #% [ ("Lam", 2) #% [ "y" \\ var 2 3 ]
                      , var 0 2
                      ]

-- match assumes that p's vars are the local end of t's
match :: Root
      -> Pat
      -> Term
      -> Maybe (Root, (Map.Map String Meta, Map.Map Meta Term))
match r (MP x ph) (t, th) = do
  let g = bigEnd th - bigEnd ph  -- how many globals?
  ps <- thicken (ones g <> ph) th
  let (m, r') = meta r x
  return (r', (Map.singleton x m, Map.singleton m (t, ps)))
match r p t = case (p, expand t) of
  (VP i, VX j _) | i == j -> return (r, (Map.empty, Map.empty))
  (AP a, AX b _) | a == b -> return (r, (Map.empty, Map.empty))
  (PP p q, s :%: t) -> do
    (r, m) <- match r p s
    (r, n) <- match r q t
    return (r, m <> n)
  (BP _ p, _ :.: t) -> match r p t
  _ -> empty

shitMeta :: String -> Meta
shitMeta s = Meta [("user",0),(s,0)]
