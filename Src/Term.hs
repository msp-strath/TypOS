{-# LANGUAGE
  DeriveTraversable,
  FlexibleInstances,
  TypeSynonymInstances,
  LambdaCase,
  TupleSections
  #-}

module Term where

import Data.List hiding ((\\))
import Control.Arrow
import Control.Monad.Writer
import Control.Monad.State
import Control.Applicative
import Data.Bits
import Data.Monoid
import Data.Traversable
import qualified Data.Map as Map

import Bwd
import Thin
import Hide

data Tm m
  = V
  | A String
  | P (RP (Tm m) (Tm m))
  | (Hide String, Bool) :. Tm m
  | m :$ Sbst m
  deriving (Show, Eq, Ord{-, Functor, Foldable, Traversable-})

instance Traversable Tm where
  traverse f V = pure V
  traverse f (A a) = pure (A a)
  traverse f (P ((s, th) :<>: (t, ph))) =
     P <$> ((:<>:) <$> ((, th) <$> traverse f s) <*> ((, ph) <$> traverse f t))
  traverse f (xb :. t) = (xb :.) <$> traverse f t
  traverse f (m :$ (sg, w)) =
    (:$) <$> f m <*> ((, w) <$> traverse f sg)
instance Functor Tm where fmap = fmapDefault
instance Foldable Tm where foldMap = foldMapDefault

newtype Meta = Meta [(String, Int)]
  deriving (Show, Ord, Eq)
type Term = CdB (Tm Meta)
type Root = (Bwd (String, Int), Int)

meta :: Root -> String -> (Meta, Root)
meta (xiz, j) x = (Meta (xiz <>> [(x, j)]), (xiz, j + 1))

infixr 3 :.
infixr 5 :$

-- relevant substitutions
type Sbst m =
  ( Sbst' m  -- what's below the weakenings
  , Int      -- how many weakenings
  )
data Sbst' m
  = S0 -- empty -> empty
  | ST (RP (Sbst m) (Hide String, Tm m))
  deriving (Show, Eq, Ord{-, Functor, Foldable, Traversable-})

instance Traversable Sbst' where
  traverse f S0 = pure S0
  traverse f (ST (((sg, w), th) :<>: ((x, t), ph))) = ST <$>
    ((:<>:) <$> ((, th) <$> ((, w) <$> traverse f sg))
            <*> ((, ph) <$> ((x,) <$>traverse f t)))
instance Functor Sbst' where fmap = fmapDefault
instance Foldable Sbst' where foldMap = foldMapDefault

-- smart constructors
sbst0 :: Int -> CdB (Sbst m)
sbst0 de = ((S0, 0), none de)
sbstW :: CdB (Sbst m) -> Th -> CdB (Sbst m)
sbstW ((sg, w), th) ph = ((sg, w + weeEnd ph), th <> ph)
sbstT :: CdB (Sbst m) -> CdB (Hide String, Tm m) -> CdB (Sbst m)
sbstT sg t = ((ST p, 0), ps) where (p, ps) = sg <&> t
sbstI :: Int -> CdB (Sbst m)
sbstI w = ((S0, w), ones w)

sbstCod :: Sbst m -> Int
sbstCod (sg, w) = case sg of
  S0 -> w
  ST ((sg, th) :<>: (t, ph)) -> bigEnd th + w

sbstSel
  :: Th -- ga0 from ga
  -> Sbst m -- ga -> de
  -> CdB (Sbst m)
sbstSel th (S0, w) = ((S0, weeEnd th), th) -- w = bigEnd th
sbstSel th (ST ((sg, phl{- del <= de -}) :<>: t), w) =
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

(//^) :: CdB (Tm m) -> CdB (Sbst m) -> CdB (Tm m)
(t, th) //^ (sg, ph) = case sbstSel th sg of
  (sg, ps) -> (t // sg, ps <^> ph)

(//) :: Tm m -> Sbst m -> Tm m
t // (S0, _) = t
V // (ST (_ :<>: ((_, t), _)), 0) = t
P ((tl, thl) :<>: (tr, thr)) // sg =
  P ((tl // sgl, phl) :<>: (tr // sgr, phr)) where
  (sgl, phl) = sbstSel thl sg
  (sgr, phr) = sbstSel thr sg
((x, b) :. t) // (sg, w) = (x, b) :. (t // (sg, if b then w+1 else w))
(m :$ rh) // sg = m :$ (rh /// sg)

(///) :: Sbst m -> Sbst m -> Sbst m
(S0, _) /// sg = sg
rh /// (S0, _) = rh
(rh, v) /// (sg, w) =
  case euclid w v of
    LtBy d -> case sg of
      ST ((sg, phl) :<>: t) ->
        (ST (((rh, d-1) /// sg, phl) :<>: t), w)
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
      ST ((rh, thl) :<>: ((x, s), thr)) -> let
        (sgl, phl) = sbstSel thl (sg, d)
        (sgr, phr) = sbstSel thr (sg, d)
        in (ST ((rh /// sgl, phl) :<>: ((x, s // sgr), phr)), v)
      {-
        -------  ;  -------
           v           v   
        -------     -------
        ----> s     -------
           rh          d   
                    -------
                       sg  
      -}


{-
-- TODO: go back to global substitutions (to avoid implicitly
-- ones-extending miss)

data Sbst m = Sbst -- from scope ga,de to terms with scope ga,xi
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
-}

-- toplevel expansions and contractions of co-deBruijn terms

data Xn m
  = VX Int
  | AX String
  | CdB (Tm m) :%: CdB (Tm m)
  | String :.: CdB (Tm m)
  | m :$: CdB (Sbst m)
  deriving (Show{-, Functor, Foldable, Traversable-})

expand :: CdB (Tm m) -> Xn m
expand (t, th) = case t of
  V   -> VX (lsb th)
  A a -> AX a
  P (s :<>: t) -> (s *^ th) :%: (t *^ th)
  (str, b) :. t -> unhide str :.: (t, th -? b)
  f :$ sg -> f :$: (sg, th)

(?:) :: CdB (Tm m) -> (Xn m -> a) -> a
t ?: f = f (expand t)

contract :: Xn m -> Int -> CdB (Tm m)
contract t ga = case t of
  VX x -> (V, inx (x, ga))
  AX a -> (A a, none ga)
  s :%: t -> P $^ (s <&> t)
  x :.: (t, th) -> case thun th of
    (th, b) -> ((Hide x, b) :. t, th)
  m :$: sg -> (m :$) $^ sg

-- smart constructors for the codeBruijn terms

var :: Int -> Int -> CdB (Tm m)
var x = contract (VX x)

atom :: String -> Int -> CdB (Tm m)
atom a = contract (AX a)

nil :: Int -> CdB (Tm m)
nil = atom ""

infixr 4 %
(%) :: (Int -> CdB (Tm m)) -> (Int -> CdB (Tm m)) -> Int -> CdB (Tm m)
(s % t) ga = contract (s ga :%: t ga) ga

(#%) :: String -> [Int -> CdB (Tm m)] -> Int -> CdB (Tm m)
(a #% ts) ga = case foldr (%) nil ts ga of
  (t, th) -> (P (atom a ga :<>: (t, ones (weeEnd th))), th)

infixr 3 \\
(\\) :: String -> (Int -> CdB (Tm m)) -> Int -> CdB (Tm m)
(x \\ t) ga = contract (x :.: t (ga+1)) ga

infixr 5 $:
($:) :: m -> (Int -> CdB (Sbst m)) -> Int -> CdB (Tm m)
(m $: sg) ga = contract (m :$: sg ga) ga


{-
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

type News = Map.Map Meta (Int, Term) -- Int is how many local vars the metavar depends on

instantiate :: News
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

-- Name generation monads

-- TODO: refactor and move into another file

class Monad m => FreshName m where
  fresh :: String -> m Meta
  nsSplit :: String -> m t -> m t

instance FreshName (State (Bwd (String, Int), Int)) where
  fresh x = do
    (root, n) <- get
    put (root, n+1)
    pure $ Meta $ root <>> [(x,n)]
  nsSplit x t = do
    (root, n) <- get
    put (root :< (x,n), 0)
    v <- t
    put (root, n+1)
    pure v

-- patterns

data Pat
  = VP
  | AP String
  | Pattern :%? Pattern
  | (Hide String, Bool) :.? Pat
  | MP String
  deriving (Show, Eq)

type Pattern = CdB Pat

{-
match :: (MonadFail m, FreshName m) => (Int, Pattern) -> Term -> m (Map.Map String Meta, News)
match (i, (p, ph)) (t, th) =
-- i is the number of bound local vars still in scope
  case p of
    MP x -> do
      let (ph', ps, th') = pullback th (apth ones (i,ph))
-}
-}

-- patterns are de Bruijn
data Pat
  = VP Int
  | AP String
  | PP Pat Pat
  | BP (Hide String) Pat
  | MP String Th
  deriving Show

-- match assumes that p's vars are the local end of t's
match :: Root -> Pat -> Term
  -> Maybe (Root, (Map.Map String Meta, Map.Map Meta Term))
match r (MP x th) (t, ph) = do
  let g = bigEnd ph - bigEnd th  -- how many globals?
  ps <- thicken (ones g <> th) ph
  let (m, r') = meta r x
  return (r', (Map.singleton x m, Map.singleton m (t, ps)))
match r p t = case (p, expand t) of
  (VP i, VX j) | i == j -> return (r, (Map.empty, Map.empty))
  (AP a, AX b) | a == b -> return (r, (Map.empty, Map.empty))
  (PP p q, s :%: t) -> do
    (r, m) <- match r p s
    (r, n) <- match r q t
    return (r, m <> n)
  (BP _ p, _ :.: t) -> match r p t
  _ -> empty


-- uglyprinting

type Naming =
  ( Bwd String  -- what's in scope *now*
  , Th          -- and how that was chosen from
  , Bwd String  -- what's been in scope ever
  )

-- The point is that when we reach a metavariable,
-- we have to document its permitted dependencies.

nameSel :: Th -> Naming -> Naming
nameSel th (xz, ph, yz) = (th ?< xz, th <^> ph, yz)

nameOn :: Naming -> String -> Naming
nameOn (xz, th, yz) x = (xz :< x, th -? True, yz :< x)

freshen :: String -> Naming -> String
freshen x (xz, _, _) = head [y | y <- ys, all (y /=) xz] where
  ys = x : [x ++ show (i :: Integer) | i <- [0..]]

display :: Show m => Naming -> Tm m -> String
display (B0 :< x, _, _) V = x
display (B0, _, _)    (A a) = case a of
  "" -> "[]"
  _  -> '\'' : a
display na (P (s :<>: (t, ph))) =
  "[" ++ display' na s ++ displayCdr (nameSel ph na) t ++ "]"
display na ((Hide x, b) :. t) = "\\" ++ case b of
  False -> "_." ++ display na t
  True  -> let y = freshen x na in
    y ++ "." ++ display (nameOn na y) t
display na (m :$ sg) = case displaySg na sg of
  [] -> "?" ++ show m
  sg' -> "{" ++ intercalate "," sg' ++ "}?" ++ show m

display' :: Show m => Naming -> CdB (Tm m) -> String
display' na (t, th) = display (nameSel th na) t

displayCdr :: Show m => Naming -> Tm m -> String
displayCdr (B0, _, _) (A "") = ""
displayCdr na (P (s :<>: (t, ph))) =
  " " ++ display' na s ++ displayCdr (nameSel ph na) t
displayCdr na t = "|" ++ display na t

displaySg :: Show m => Naming -> Sbst m -> [String]
displaySg (_, th, _) (S0, _)
  | th == ones (bigEnd th) = []
displaySg na (ST ((sg, th) :<>: ((Hide x, t), ph)), 0) =
  (x ++ "=" ++ display' na (t, ph)) :
  displaySg (nameSel th na) sg
displaySg (xz, th, yz :< y) (sg, w) = case thun th of
  (th, False) ->
    (y ++ "*") : displaySg (xz, th, yz) (sg, w)
  (th, True) ->
    case xz of
      xz :< x ->
        x : displaySg (xz, th, yz) (sg, w - 1)



-----------------------------
