{-# LANGUAGE
  DeriveTraversable,
  FlexibleInstances,
  TypeSynonymInstances,
  LambdaCase
  #-}

module Term where

import Data.List hiding ((\\))
import Control.Arrow
import Control.Monad.Writer
import Data.Bits
import Data.Monoid
import qualified Data.Map as Map

import Bwd
import Thin
import Hide

data Tm m
  = V
  | A String
  | CdB (Tm m) :% CdB (Tm m)
  | (Hide String, Bool) :. Tm m
  | m :$ Sbst m
  deriving (Show, Eq, Functor, Foldable, Traversable)

newtype Meta = Meta [(String, Int)]
  deriving (Show, Ord, Eq)
type Term = CdB (Tm Meta)

infixr 3 :.
infixr 4 :%
infixr 5 :$

data Sbst m = Sbst -- from scope ga,de to terms with support ga,xi
 { hits :: Th -- which things in de we hit
 , imgs :: Bwd (CdB (Tm m)) -- images of what we hit
 , miss :: Th -- how the missed things in ga,de embed in ga,xi (identity on ga)
 } deriving (Show, Eq, Functor, Foldable, Traversable)
-- invariant: the target scope is covered by the
-- imgs thinnings and miss
-- invariant: miss is ones-extended as if ga is infinite

newtype CdBS m = CdBS (CdB (Sbst m))
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- smart constructor for codeBruijn substitution
sbst :: Th -> Bwd (CdB (Tm m)) -> Th -> CdBS m
sbst th iz ph = CdBS (Sbst th iz' ph', ps) where
  (jz, ps0) = copz iz
  ((ps1, ph'), ps) = cop ps0 ph
  iz' = fmap (*^ ps1) jz

-- toplevel expansions and contractions of co-deBruijn terms

data Xn m
  = X Int
  | AX String
  | CdB (Tm m) :%: CdB (Tm m)
  | String :.: CdB (Tm m)
  | m :$: Sbst m
  deriving (Show, Functor, Foldable, Traversable)

expand :: CdB (Tm m) -> Xn m
expand (t, th) = case t of
  V   -> X (lsb th)
  A a -> AX a
  s :% t -> (s *^ th) :%: (t *^ th)
  (str, b) :. t -> unhide str :.: (t, th -? b)
  f :$ sg -> f :$: (sg {imgs = fmap (*^ th) (imgs sg), miss = miss sg <> th })

(?:) :: CdB (Tm m) -> (Xn m -> a) -> a
t ?: f = f (expand t)

contract :: Xn m -> CdB (Tm m)
contract = \case
  X x -> (V, inx x)
  AX a -> (A a, none)
  (s, th) :%: (t, ph) -> case cop th ph of
    ((th, ph), ps) -> ((s, th) :% (t, ph), ps)
  x :.: (t, th) -> case thun th of
    (th, b) -> ((Hide x, b) :. t, th)
  m :$: (Sbst hits imgs miss) -> m $^ (sbst hits imgs miss)

-- smart constructors for the codeBruijn terms

var :: Int -> CdB (Tm m)
var x = contract (X x)

atom :: String -> CdB (Tm m)
atom a = contract (AX a)

nil :: CdB (Tm m)
nil = atom ""

infixr 4 %
(%) :: CdB (Tm m) -> CdB (Tm m) -> CdB (Tm m)
s % t = contract (s :%: t)

(#%) :: String -> [CdB (Tm m)] -> CdB (Tm m)
a #% ts = case foldr (%) nil ts of
  (t, th) -> (atom a :% (t, ones), th)

infixr 3 \\
(\\) :: String -> CdB (Tm m) -> CdB (Tm m)
x \\ t = contract (x :.: t)

infixr 5 $:
($:) :: m -> Sbst m -> CdB (Tm m)
m $: sg = contract (m :$: sg)

($^) :: m -> CdBS m -> CdB (Tm m)
m $^ (CdBS (sg, th)) = (m :$ sg, th)

-- co-smart destructors for the codeBruijn terms

car, cdr :: CdB (Tm m) -> CdB (Tm m)
car (s :% _, ph) = s *^ ph
cdr (_ :% t, ph) = t *^ ph

tag :: CdB (Tm m) -> String
tag (A a, _) = a

(%<) :: CdB (Tm m) -> (CdB (Tm m) -> CdB (Tm m) -> a) -> a
t %< f = f (car t) (cdr t)

(#%<) :: CdB (Tm m) -> (String -> CdB (Tm m) -> a) -> a
t #%< f = t %< (f . tag)

under :: CdB (Tm m) -> CdB (Tm m)
under ((_, b) :. t, th) = (t, th -? b)

-- smart constructors for the codeBruijn substs

wkSbst :: CdBS m -> CdBS m
wkSbst (CdBS (Sbst { hits = th, imgs = iz, miss = ph }, ps))
  = CdBS (Sbst
  { hits = th -? False
  , imgs = fmap weak iz
  , miss = ph -? True
  }, ps -? True)

topSbst :: CdB (Tm m) -> CdBS m
topSbst t = CdBS (Sbst
  { hits = none -? True
  , imgs = B0 :< t
  , miss = ones
  }, ones)

instance Monoid (CdBS m) where
  mempty = sbst none B0 ones
  mappend
    (CdBS (Sbst { hits = th0, imgs = iz0, miss = ph0 }, ps0))
    ta
    = CdBS
      (Sbst { hits = th
            , imgs = riffle (iz0', th0i) (ph0' ?< iz1, mui)
            , miss = ph0'' <> ph1 }
      , ps1)
    where
    ta'@(CdBS (Sbst { hits = th1, imgs = iz1, miss = ph1 }, ps1)) =
      ps0 ?// ta
    (th1', _, ph0') = pullback ph0 th1
    mu = th1' <> comp th0 -- missed by front hit by back
    ((th0i, mui), th) = cop th0 mu
    iz0' = fmap (^// ta') iz0
    (_, _, ph0'') = pullback ph0 (comp th1)

instance Semigroup (CdBS m) where (<>) = mappend

-- restrict the source of a substitution
--  gaa ---th---> ga <---~th--- gap ---ph;ps---> de
--   ^             ^             ^
--   |             |             |
--  ch'           ch            pi'
--   |[]           |           []|
--  gaa' --th'--> ga' <-------- gap'
(?//) :: Th -> CdBS m -> CdBS m
ch ?// (CdBS (Sbst { hits = th, imgs = iz, miss = ph }, ps)) =
  sbst th' iz' ph' //^ ps where
  (th', _, ch') = pullback ch th
  (_, _, pi') = pullback ch (comp th)
  ph' = pi' <> ph
  iz' = ch' ?< iz

-- thinning the target of a substitution
(//^) :: CdBS m -> Th -> CdBS m
CdBS sg //^ th = CdBS (sg *^ th)

-- action of codeBruijn substitution ga => de
-- on codeBruijn term
(^//) :: CdB (Tm m) -> CdBS m -> CdB (Tm m)
(t, th) ^// sg =
  if   hits ta == none
  then (t, ps)  -- miss ta = ones if hits ta = none
  else t // taph
  where
  -- restrict substitution to support of source term
  taph@(CdBS (ta, ps)) = th ?// sg

-- the worker: presumes we've already restricted
-- to support and have things to hit
(//) :: Tm m -> CdBS m -> CdB (Tm m)
V // (CdBS (Sbst {imgs = (B0 :< t)}, ps)) = t *^ ps
(s :% t) // sg = (s ^// sg) % (t ^// sg)
((Hide x, False) :. t) // sg = x \\ (t // sg)
((Hide x, True) :. t) // sg = x \\ (t // wkSbst sg)
(m :$ ta) // sg = m $^ (CdBS (ta, ones) <> sg)
-- t // sg = error (show t ++ " // " ++ show sg)

-- Mangling terms

data Mangler f = Mangler
  { mangX :: Int -> f Term
  , mangM :: Meta -> Sbst Meta -> f Term -- mangM needs to recursively deal with subst if needed
  , mangB :: String -> Mangler f
  }

mangle :: Applicative f => Mangler f -> Term -> f Term
mangle mangler@(Mangler mangX mangM mangB) t = t ?: \case
  X i -> mangX i
  AX a -> pure (atom a)
  t0 :%: t1 -> (%) <$> mangle mangler t0 <*> mangle mangler t1
  x :.: t -> (x \\) <$> mangle (mangB x) t
  m :$: sg -> mangM m sg

-- meta variable instantiation

instantiate :: Map.Map Meta (Int, Term) -- Int is how many local vars the metavar depends on
            -> Term                     -- term to instantiate in
            -> (Bool, Term)             -- (did it change?, instantiated term)
instantiate metas t = (getAny b, r) where
  (r, b) = runWriter (mangle (mangler ones) t)
  mangler :: Th -> Mangler (Writer Any)
  -- theta : Gamma -> Gamma'
  mangler th = Mangler
    { mangX = pure . var
    , mangB = \ x -> mangler (th -? False)
    , mangM = \ m (Sbst hits imgs misses) -> do
        imgs' <- traverse (mangle (mangler th)) imgs
        let sg' = sbst hits imgs' misses
        case Map.lookup m metas of
          Nothing -> pure (m $^ sg')
          Just (i, t) -> do
            tell (Any True)
            pure $ (t *^ apth th (i,ones)) ^// sg'
    }

-- uglyprinting

display :: Show m => Bwd String -> Tm m -> String
display (B0 :< x) V = x
display B0    (A a) = case a of
  "" -> "[]"
  _  -> '\'' : a
display xz (s :% (t, ph)) =
  "[" ++ display' xz s ++ displayCdr (ph ?< xz) t ++ "]"
display xz ((Hide x, b) :. t) = "\\" ++ case b of
  False -> "_." ++ display xz t
  True  -> case mangle xz [] of
    x -> x ++ "." ++ display (xz :< x) t
 where
  mangle B0 ss = if elem "" ss then vary 0 ss else x
  mangle (yz :< y) ss = case stripPrefix x y of
    Nothing -> mangle yz ss
    Just s -> mangle yz (s : ss)
  vary :: Int -> [String] -> String
  vary i ss = if elem y ss then vary (i + 1) ss else y where y = x ++ show i
display xz (m :$ sg) = concat
  [show m, "{", intercalate ", " (displaySg xz sg <>> []), "}"]

display' :: Show m => Bwd String -> CdB (Tm m) -> String
display' xz (t, th) = display (th ?< xz) t

displayCdr :: Show m => Bwd String -> Tm m -> String
displayCdr B0 (A "") = ""
displayCdr xz (s :% (t, ph)) =
  " " ++ display' xz s ++ displayCdr (ph ?< xz) t
displayCdr xz t = "|" ++ display xz t

displaySg :: Show m => Bwd String -> Sbst m -> Bwd String
displaySg xz (Sbst th iz ph)
  | th == none = B0
  | otherwise = case thun th of
    (th, False) -> case ph ?< xz of
      _ :< x -> displaySg xz (Sbst th iz (nip ph)) :< x
    (th, True) -> case iz of
      (iz :< t') ->
        displaySg xz (Sbst th iz ph) :<
        display' xz t'
  where
    nip th
      | th == none = error "nipping none"
      | otherwise = case thun th of
        (th, True)  -> th -? False
        (th, False) -> nip th -? False

-----------------------------
