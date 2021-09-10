module Basics where

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
{-# BUILTIN EQUALITY _~_ #-}

refl : {X : Set}(x : X) -> x ~ x
refl x = r~

_~$~_ : forall {S T}
  {f g : S -> T} -> f ~ g ->
  {x y : S} -> x ~ y ->
  f x ~ g y
r~ ~$~ r~ = r~
infixl 2 _~$~_

id : forall {l}{X : Set l} -> X -> X
id x = x

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A) -> C a (f a)
(f - g) a = g (f a)

ko : forall {i j}{A : Set i}{B : A -> Set j}
  (a : A)(b : B a) -> A
ko a _ = a

data `0 : Set where
record `1 : Set where constructor <>
data `2 : Set where ff tt : `2

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X
infixl 30 _-,_ _<<<_

_<<<_ : forall {X} -> Bwd X -> Bwd X -> Bwd X
xz <<< [] = xz
xz <<< (yz -, y) = xz <<< yz -, y

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
pattern !_ t = _ , t
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
pattern _&_ a b = ! a , b
infixr 10 _><_ !_ _,_ _*_
infixr 11 _&_
_+_ : Set -> Set -> Set
S + T = `2 >< \ { ff -> S ; tt -> T }
Maybe = `1 +_
pattern aye x = tt , x
pattern naw   = ff , <>

_>><<_ : forall {S0 S1 T0 T1} -> (f : S0 -> S1)(g : forall {s0} -> T0 s0 -> T1 (f s0)) ->
  S0 >< T0 -> S1 >< T1
(f >><< g) (s , t) = f s , g t

maybe : forall {S T} -> (S -> T) -> Maybe S -> Maybe T
maybe f naw = naw
maybe f (aye s)  = aye (f s)

_>M=_ : forall {S T} -> Maybe S -> (S -> Maybe T) -> Maybe T
aye s >M= k = k s
naw   >M= k = naw

pure : forall {X} -> X -> Maybe X
_<*>_ : forall {S T} -> Maybe (S -> T) -> Maybe S -> Maybe T
pure x = aye x
f <*> s = f >M= \ f -> s >M= \ s -> aye (f s)


module _ {X : Set} where

  <_> [_] : (X -> Set) -> Set
  < T > = X >< T
  [ T ] = {x : X} -> T x
  infixr 10 <_> [_]

  _*:_ _-:>_ : (X -> Set) -> (X -> Set) -> (X -> Set)
  (S *: T) x = S x * T x
  (S -:> T) x = S x -> T x
  infixr 10 _*:_
  infixr 9 _-:>_
