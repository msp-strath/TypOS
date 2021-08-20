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
            <*> ((, ph) <$> ((x,) <$> traverse f t)))
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
match r (MP x ph) (t, th) = do
  let g = bigEnd th - bigEnd ph  -- how many globals?
  ps <- thicken (ones g <> ph) th
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
  ( Bwd String  -- what's in the support 
  , Th          -- and how that was chosen from
  , Bwd String  -- what's in scope
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
