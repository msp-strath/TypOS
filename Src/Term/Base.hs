module Term.Base where

import Data.Traversable
import Data.Void

import Bwd
import Thin
import Hide

data Tm m
  = V
  | A String
  | P (RP (Tm m) (Tm m))
  | (:.) (Named Bool) (Tm m)
  | m :$ Sbst m
  deriving (Show, Eq, Ord)

instance Traversable Tm where
  traverse f V = pure V
  traverse f (A a) = pure (A a)
  traverse f (P (CdB s th :<>: CdB t ph)) =
     P <$> ((:<>:) <$> (CdB <$> traverse f s <*> pure th)
                   <*> (CdB <$> traverse f t <*> pure ph))
  traverse f (xb :. t) = (xb :.) <$> traverse f t
  traverse f (m :$ (sg :^^ w)) =
    (:$) <$> f m <*> ((:^^ w) <$> traverse f sg)
instance Functor Tm where fmap = fmapDefault
instance Foldable Tm where foldMap = foldMapDefault

isMetaFree :: CdB (Tm m) -> Maybe (CdB (Tm Void))
isMetaFree (CdB t th) = (`CdB` th) <$> traverse (const Nothing) t

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
  traverse f (ST (CdB sg th :<>: CdB t ph)) = ST <$>
    ((:<>:) <$> (CdB <$> traverse f sg <*> pure th)
            <*> (CdB <$> traverse (traverse f) t <*> pure ph))
instance Functor Sbst' where fmap = fmapDefault
instance Foldable Sbst' where foldMap = foldMapDefault

-- smart constructors
sbst0 :: Int -> CdB (Sbst m)
sbst0 de = CdB (S0 :^^ 0) (none de)

sbstW :: CdB (Sbst m) -> Th -> CdB (Sbst m)
sbstW (CdB (sg :^^ w) th) ph = CdB (sg :^^ (w + weeEnd ph)) (th <> ph)

sbstT :: CdB (Sbst m) -> CdB (Named (Tm m)) -> CdB (Sbst m)
sbstT sg t = CdB (ST p :^^ 0) ps where CdB p ps = sg <&> t

sbstI :: Int -> CdB (Sbst m)
sbstI w = CdB (S0 :^^ w) (ones w)

topSbst :: String -> CdB (Tm m) -> CdB (Sbst m)
topSbst x t = sbstT (sbstI (scope t)) ((Hide x :=) $^ t)

sbstCod :: Sbst m -> Int
sbstCod (sg :^^ w) = case sg of
  S0 -> w
  ST (sg :<>: t) -> scope sg + w

sbstDom :: Sbst m -> Int
sbstDom (sg :^^ w) = case sg of
 S0 -> w
 ST (CdB sg th :<>: t) -> sbstDom sg + 1 + w

sbstSel
  :: Th -- ga0 from ga
  -> Sbst m -- ga -> de
  -> CdB (Sbst m)
sbstSel th (S0 :^^ w) = CdB (S0 :^^ weeEnd th) th -- w = bigEnd th
sbstSel th (ST (CdB sg phl{- del <= de -} :<>: t) :^^ w) =
  sbstW (if b then sbstT sg0 t else sg0) thw
  where
  -- ga, x, w -> de, w
  (thgax, thw) = thChop th w
  (thga, b) = thun thgax
  sg0 = sbstSel thga sg *^ phl

-- toplevel expansions and contractions of co-deBruijn terms

data Xn m
  = VX DB Int    -- which free variable out of how many?
  | AX String Int -- how many free variables?
  | CdB (Tm m) :%: CdB (Tm m)
  | String :.: CdB (Tm m)
  | m :$: CdB (Sbst m)
  deriving (Eq, Show{-, Functor, Foldable, Traversable-})

expand :: CdB (Tm m) -> Xn m
expand (CdB t th) = case t of
  V   -> VX (lsb th) (bigEnd th)
  A a -> AX a (bigEnd th)
  P (s :<>: t) -> (s *^ th) :%: (t *^ th)
  (str := b) :. t -> unhide str :.: CdB t (th -? b)
  f :$ sg -> f :$: CdB sg th

(?:) :: CdB (Tm m) -> (Xn m -> a) -> a
t ?: f = f (expand t)

contract :: Xn m -> CdB (Tm m)
contract t = case t of
  VX x ga -> CdB V (inx (x, ga))
  AX a ga -> CdB (A a) (none ga)
  s :%: t -> P $^ (s <&> t)
  x :.: CdB t th -> case thun th of
    (th, b) -> CdB ((Hide x := b) :. t) th
  m :$: sg -> (m :$) $^ sg

-- smart constructors for the codeBruijn terms; bigEnds must agree

var :: DB -> Int -> CdB (Tm m)
var x ga = contract (VX x ga)

atom :: String -> Int -> CdB (Tm m)
atom a ga = contract (AX a ga)

nil :: Int -> CdB (Tm m)
nil = atom ""

infixr 4 %
(%) :: CdB (Tm m) -> CdB (Tm m) -> CdB (Tm m)
s % t = contract (s :%: t)

(#%) :: (String, Int) -> [CdB (Tm m)] -> CdB (Tm m)
(a, ga) #% ts = uncurry CdB $ case foldr (%) (nil ga) ts of
  CdB t th -> (P (atom a ga :<>: CdB t (ones (weeEnd th))), th)

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

asNilOrCons :: OrBust x => x -> (CdB (Tm m) -> CdB (Tm m) -> x) -> CdB (Tm m) -> x
asNilOrCons nil cons t = t ?: \case
  x :%: xs -> cons x xs
  AX "" _ -> nil
  _ -> bust

asList :: OrBust x => ([CdB (Tm m)] -> x) -> CdB (Tm m) -> x
asList f = asNilOrCons (f []) (\ x -> asList (f . (x:)))

infixr 3 \\
(\\) :: String -> CdB (Tm m) -> CdB (Tm m)
x \\ t = contract (x :.: t)

infixr 5 $:
($:) :: m -> CdB (Sbst m) -> CdB (Tm m)
m $: sg = contract (m :$: sg)

shitMeta :: String -> Meta
shitMeta s = Meta [("user",0),(s,0)]
