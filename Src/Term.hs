{-# LANGUAGE
  DeriveTraversable,
  FlexibleInstances,
  TypeSynonymInstances
  #-}

module Term where

import Data.List hiding ((\\))
import Control.Arrow
import Data.Bits

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

infixr 3 :.
infixr 4 :%
infixr 5 :$

data Sbst m = Sbst -- from scope ga to terms with support de
 { hits :: Th -- which things in ga we hit
 , imgs :: Bwd (CdB (Tm m)) -- images of what we hit
 , miss :: Th -- how the missed things embed in de
 } deriving (Show, Eq, Functor, Foldable, Traversable)
-- invariant: the target scope is covered by the
-- imgs thinnings and miss

newtype CdBS m = CdBS (CdB (Sbst m))

-- smart constructor for codeBruijn substitution
sbst :: Th -> Bwd (CdB (Tm m)) -> Th -> CdBS m
sbst th iz ph = CdBS (Sbst th iz' ph', ps) where
  (jz, ps0) = copz iz
  ((ps1, ph'), ps) = cop ps0 ph
  iz' = fmap (*^ ps1) jz

-- smart constructors for the codeBruijn terms

var :: Int -> CdB (Tm m)
var x = (V, inx x)

atom :: String -> CdB (Tm m)
atom a = (A a, none)

nil :: CdB (Tm m)
nil = atom ""

infixr 4 %
(%) :: CdB (Tm m) -> CdB (Tm m) -> CdB (Tm m)
(s, th) % (t, ph) = case cop th ph of
  ((th, ph), ps) -> ((s, th) :% (t, ph), ps)

li :: [CdB (Tm m)] -> CdB (Tm m)
li = foldr (%) nil

infixr 3 \\
(\\) :: String -> CdB (Tm m) -> CdB (Tm m)
x \\ (t, th) = case thun th of
  (th, b) -> ((Hide x, b) :. t, th)

infixr 5 $:
($:) :: m -> CdBS m -> CdB (Tm m)
m $: (CdBS (sg, th)) = (m :$ sg, th)

wkSbst :: CdBS m -> CdBS m
wkSbst (CdBS (Sbst { hits = th, imgs = iz, miss = ph }, ps))
  = CdBS (Sbst
  { hits = th -? False
  , imgs = fmap (id *** (-? False)) iz
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
            , imgs = riffle (iz0', th0i) (iz1, mui)
            , miss = ph0' <> ph1 }
      , ps1)
    where
    ta'@(CdBS (Sbst { hits = th1, imgs = iz1, miss = ph1 }, ps1)) =
      ps0 ?// ta
    (th1', _, _) = pullback ph0 th1
    mu = th1' <> comp th0 -- missed by front hit by back
    ((th0i, mui), th) = cop th0 mu
    iz0' = fmap (^// ta') iz0
    (_, _, ph0') = pullback ph0 (comp th1)
    
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
  then (t, ps)
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
(m :$ ta) // sg = m $: (CdBS (ta, ones) <> sg)



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
