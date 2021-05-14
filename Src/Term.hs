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

data TmF m tm
  = V
  | A String
  | CdB tm :% CdB tm
  | (Hide String, Bool) :. tm
  | m :$ Sbst tm
  deriving (Show, Eq, Functor, Foldable, Traversable)

infixr 3 :.
infixr 4 :%
infixr 5 :$

data Tm m = T (TmF m (Tm m)) deriving (Show, Eq)

data Sbst tm = Sbst -- from scope ga to terms in scope de
 { hits :: Th -- which things in ga we hit
 , imgs :: CdB (Bwd (CdB tm)) -- images of what we hit
   -- inner thinnings embed image support into union thereof
   -- outer thinning embeds union of supports into de
 , miss :: Th -- how the missed things embed in de
 } deriving (Show, Eq, Functor, Foldable, Traversable)

-- smart constructors for the codeBruijn terms

var :: Int -> CdB (Tm m)
var x = (T V, inx x)

atom :: String -> CdB (Tm m)
atom a = (T (A a), none)

nil :: CdB (Tm m)
nil = atom ""

infixr 4 %
(%) :: CdB (Tm m) -> CdB (Tm m) -> CdB (Tm m)
(s, th) % (t, ph) = case cop th ph of
  ((th, ph), ps) -> (T ((s, th) :% (t, ph)), ps)

li :: [CdB (Tm m)] -> CdB (Tm m)
li = foldr (%) nil

infixr 3 \\
(\\) :: String -> CdB (Tm m) -> CdB (Tm m)
x \\ (t, th) = case thun th of
  (th, b) -> (T ((Hide x, b) :. t), th)

infixr 5 $:
($:) :: m -> Sbst (Tm m) -> CdB (Tm m)
m $: Sbst th (iz, ps) ph =
  (T (m :$ Sbst th (iz, ps') ph'), ch) where
  ((ps', ph'), ch) = cop ps ph

wkSbst :: Sbst t -> Sbst t
wkSbst (Sbst { hits = th, imgs = (iz, ps), miss = ph }) = Sbst
  { hits = th -? False
  , imgs = (iz, ps -? False)
  , miss = ps -? True
  }

topSbst :: CdB t -> Sbst t
topSbst (t, th) = Sbst
  { hits = none -? True
  , imgs = (B0 :< (t, ones), th)
  , miss = ones
  }

instance Monoid (Sbst (Tm m)) where
  mempty = Sbst
    { hits = none
    , imgs = (B0, none)
    , miss = ones
    }
  mappend
    (Sbst { hits = th0, imgs = (iz0, ps0), miss = ph0 })
    ta@(Sbst { hits = th1, imgs = (iz1, ps1), miss = ph1 })
    = Sbst
    { hits = _
    , imgs = _
    , miss = _
    } where
    (th1', _, ph0') = pullback ph0 th1
    (_, _, _) = pullback ph0 (comp th1)
    
instance Semigroup (Sbst (Tm m)) where (<>) = mappend

(^//) :: CdB (Tm m) -> Sbst (Tm m) -> CdB (Tm m)
(t, th) ^// sg =
  if hits ta == none then (t, miss ta) else t // ta
  where
  ta = th ?// sg

(?//) :: Th -> Sbst t -> Sbst t
th ?// Sbst { hits = ph, imgs = (iz, ps), miss = ch } = Sbst
  { hits = ph'
  , imgs = (jz, ps' <> ps)
  , miss = om <> ch
  } where
  (ph', _, th') = pullback th ph
  (_, _, om)    = pullback th (comp ph)
  (jz, ps') = copz (th' ?< iz)

(//) :: Tm m -> Sbst (Tm m) -> CdB (Tm m)
T V // Sbst {imgs = (B0 :< (t, _), th)} = (t, th)
T (s :% t) // sg = (s ^// sg) % (t ^// sg)
T ((Hide x, False) :. t) // sg = x \\ (t // sg)
T ((Hide x, True) :. t) // sg = x \\ (t // wkSbst sg)
T (m :$ ta) // sg = m $: (ta <> sg)



-- uglyprinting

display :: Show m => Bwd String -> Tm m -> String
display (B0 :< x) (T V) = x
display B0    (T (A a)) = case a of
  "" -> "[]"
  _  -> '\'' : a
display xz (T (s :% (t, ph))) =
  "[" ++ display' xz s ++ displayCdr (ph ?< xz) t ++ "]"
display xz (T ((Hide x, b) :. t)) = "\\" ++ case b of
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
display xz (T (m :$ sg)) = concat
  [show m, "{", intercalate ", " (displaySg xz sg <>> []), "}"]

display' :: Show m => Bwd String -> CdB (Tm m) -> String
display' xz (t, th) = display (th ?< xz) t

displayCdr :: Show m => Bwd String -> Tm m -> String
displayCdr B0    (T (A "")) = ""
displayCdr xz (T (s :% (t, ph))) =
  " " ++ display' xz s ++ displayCdr (ph ?< xz) t
displayCdr xz t = "|" ++ display xz t

displaySg :: Show m => Bwd String -> Sbst (Tm m) -> Bwd String
displaySg xz (Sbst th (iz, ps) ph)
  | th == none = B0
  | otherwise = case thun th of
    (th, False) -> case ph ?< xz of
      _ :< x -> displaySg xz (Sbst th (iz, ps) (nip ph)) :< x
    (th, True) -> case iz of
      (iz :< t') ->
        displaySg xz (Sbst th (iz, ps) ph) :<
        display' xz (t' *^ ps)
  where
    nip th
      | th == none = error "nipping none"
      | otherwise = case thun th of
        (th, True)  -> th -? False
        (th, False) -> nip th -? False
