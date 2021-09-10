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

import Data.List hiding ((\\))
import Data.Maybe (fromMaybe)
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

import Debug.Trace

track = const id -- trace

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

data Mangler m f = Mangler
  { mangSrc :: Int               -- size of source scope
  , mangTgt :: Int               -- size of target scope
  , mangTh :: Maybe Th           -- are you just embedding src into tgt?
  , mangV :: f (CdB (Tm m))      -- how to replace variables
  , mangB :: Mangler m f         -- how to mangle under a relevant binder
  , mangM :: m -> f (CdB (Sbst m)) -> f (CdB (Tm m))
    -- how to replace a meta & mangled substitution
  , mangW :: Int -> Mangler m f  -- how to undo some `mangB`s
  , mangSelFrom :: Th                -- big end should be mangSrc
                -> Mangler m f       -- source of output mangler
                                     --   should be the wee end of the input
                                     --   thinnings; target stays put
  }

stanMangler
  :: Show m
  => Ord m
  -- Γ: in scope at the root of the term we're traversing
  -- ξ: binders we've gone under
  -- θ: support of the term we're traversing
  => Th                      -- θ ⊆ Γ, ξ
  -> Th                      -- Γ ⊆ Γ, ξ
  -> Map.Map m ( Int         -- i: # of variables captured by the meta
               , CdB (Tm m)) -- (Γ, [1..i])-term to replace the meta with
  -> Mangler m (Writer Any)  -- (Γ, ξ) terms factory
stanMangler th emb tbl = Mangler
  { mangSrc = bigEnd th
  , mangTgt = bigEnd th
  , mangTh = th <$ guard (null tbl)
  , mangV = pure (V, th)
  , mangB = stanMangler (th -? True) (emb -? False) tbl
  , mangM = \ m sg ->
      case Map.lookup m tbl of
        Nothing -> (m $:) <$> sg
        Just (i, t) -> ((t *^ (emb <> ones i)) //^) <$> sg <* tell (Any True)
  , mangW = \ w -> stanMangler (fst $ thChop th w) (fst $ thChop emb w) tbl
  , mangSelFrom = \ ph -> stanMangler (ph <^> th) emb tbl
  }

class Manglable m t where
  mangle  :: Applicative f => Mangler m f -> t -> f (CdB t)
  -- mangle' is worker for mangle
  mangle' :: Applicative f => Mangler m f -> t -> f (CdB t)
  -- Int is size of the target scope
  mangleCdB :: Applicative f => Mangler m f -> CdB t -> f (CdB t)

  mangle mu t = case mangTh mu of
    Just th -> pure (t, th)
    Nothing -> mangle' mu t

  mangleCdB mu (t, th) = mangle mu' t where
    -- we recheck for mangI after doing a selection computing m'
    mu' = mangSelFrom mu th

instance Manglable m a => Manglable m (Named a) where
  mangle' mu (x := a) = ((x :=) $^) <$> mangle' mu a

instance Manglable m (Tm m) where
  mangle' mu V = mangV mu
  mangle' mu (A a) = pure (atom a (mangTgt mu))
  mangle' mu (P p) = (P $^) <$> mangle' mu p
  mangle' mu ((Hide x := False) :. t) = (x \\) <$> (weak <$> mangle' mu t)
  mangle' mu ((Hide x := True) :. t) = (x \\) <$> mangle' (mangB mu) t
  mangle' mu (m :$ sg) = mangM mu m (mangle' mu sg)

instance (Manglable m a, Manglable m b) => Manglable m (RP a b) where
  mangle' mu (a :<>: b)  = (<&>) <$> mangleCdB mu a <*> mangleCdB mu b

newtype Meta = Meta [(String, Int)]
  deriving (Show, Ord, Eq)
type Term = CdB (Tm Meta)
type Root = ( Bwd (String, Int) -- name prefix
            , Int)              -- counter

initRoot :: Root
initRoot = (B0, 0)

-- fresh meta in the current root space
meta :: Root -> String -> (Meta, Root)
meta (xiz, j) x = (Meta (xiz <>> [(x, j)]), (xiz, j + 1))

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

instance Manglable m (Sbst m) where
  mangle' mu (sg :^^ w) = sbstW <$> sg' <*> pure (ones w) where
    mu' = mangW mu w
    sg' = case sg of
      S0 -> pure (sbstI (mangTgt mu'))
            -- ^ used to be sbst0
            -- this is more in line with pure (ones w) above
            -- & seems to fix the beta test case
            -- NEED: Agda model!
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
  deriving (Show{-, Functor, Foldable, Traversable-})

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

infixr 3 \\
(\\) :: String -> CdB (Tm m) -> CdB (Tm m)
x \\ t = contract (x :.: t)

infixr 5 $:
($:) :: m -> CdB (Sbst m) -> CdB (Tm m)
m $: sg = contract (m :$: sg)


-- patterns are de Bruijn
data Pat
  = VP Int
  | AP String
  | PP Pat Pat
  | BP (Hide String) Pat
  | MP String Th
  deriving Show

(#?) :: String -> [Pat] -> Pat
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
  let ga = scope t
  let rhs = (fmap (trustMe m) $^ betaRHS) *^ none ga
  track (show rhs) $ pure ()
  let (res, _) = runWriter $ mangleCdB (stanMangler (ones ga) (ones ga) val) rhs
  pure (r, res)

  where

    trustMe :: Ord a => Map.Map a b -> (a -> b)
    trustMe m v = fromMaybe (error "IMPOSSIBLE") (Map.lookup v m)

redex :: Term
redex = ("App", 1) #% [ ("Lam", 1) #% [ "y" \\ var 0 2 ]
                      , var 0 1
                      ]

-- match assumes that p's vars are the local end of t's
match :: Root
      -> Pat
      -> Term
      -> Maybe (Root, (Map.Map String Meta, Map.Map Meta (Int, Term)))
match r (MP x ph) (t, th) = do
  let g = bigEnd th - bigEnd ph  -- how many globals?
  ps <- thicken (ones g <> ph) th
  let (m, r') = meta r x
  return (r', (Map.singleton x m, Map.singleton m (weeEnd ph, (t, ps))))
match r p t = case (p, expand t) of
  (VP i, VX j _) | i == j -> return (r, (Map.empty, Map.empty))
  (AP a, AX b _) | a == b -> return (r, (Map.empty, Map.empty))
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

initNaming :: Naming
initNaming = (B0, ones 0, B0)

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
display na ((Hide x := b) :. t) = "\\" ++ case b of
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
displaySg (_, th, _) (S0 :^^ _)
  | th == ones (bigEnd th) = []
displaySg na (ST ((sg, th) :<>: ((Hide x := t), ph)) :^^ 0) =
  (x ++ "=" ++ display' na (t, ph)) :
  displaySg (nameSel th na) sg
displaySg (xz, th, yz :< y) (sg :^^ w) = case thun th of
  (th, False) ->
    (y ++ "*") : displaySg (xz, th, yz) (sg :^^ w)
  (th, True) ->
    case xz of
      xz :< x ->
        x : displaySg (xz, th, yz) (sg :^^ (w - 1))

displayCdB :: Show m => Naming -> CdB (Tm m) -> String
displayCdB nm (t, th) = "(" ++ display nm t ++ ", " ++ show th ++ ")"

-----------------------------
