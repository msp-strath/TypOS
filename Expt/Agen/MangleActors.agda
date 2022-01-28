module MangleActors where

open import Basics
open import Thin
open import Cop
open import Pair
open import Bind
open import Pub

open THIN {`1}
open COP  {`1}
open PAIR {`1}
open BIND {`1}
open PUB  {`1}
open import Term

postulate ActorVar Unknown : Nat -> Set
postulate ATOM : Set

module _ where

  open TERM ActorVar ATOM

  Src : Nat -- scope from the pattern that bound it
     -> Set
  Src = Tm
  _S>_ = _%>_
  _S>^_ = _%>^_

module _ where

  open TERM Unknown ATOM

  Trg : Nat -- what's actually in scope?
     -> Set
  Trg = Tm
  _T>_ = _%>_
  _T>^_ = _%>^_

Env : Nat -> Set
Env ga = forall {xi}
      -> ActorVar xi
      -> Trg ^: (ga <<< xi)

module T {M} = TERM M ATOM
open T

ma : forall
     {de0 -- support of source term
      de  -- how many binders in source term we're under
      ga  -- how many vars are really in scope
     }
  -> Src de0
  -> de0 <= de
  -> Env ga
  -> Trg ^: (ga <<< de)

masu : forall
     {xi  -- scope of actor var
      de0 -- support of source term
      de  -- how many binders in source term we're under
      ga  -- how many vars are really in scope
     }
  -> xi S> de0
  -> de0 <= de
  -> Env ga
  -> (ga <<< xi) T>^ (ga <<< de)

ma (vv only) th rh = v^ (no +^+ th)
ma (aa (atom a)) th rh = a^ a
ma (pp (s </ u \> t)) th rh =
  ma s (luth u -& th) rh ,^ ma t (ruth u -& th) rh
ma (bb (kk t)) th rh = b^ (ma t (th -^ <>) rh)
ma (bb (ll t)) th rh = b^ (ma t (th -, <>) rh)
ma (mm (x & sg)) th rh = rh x //^ masu sg th rh

masu [] th rh = is & io{-ga-} +^+ no{-de-}
masu (sg -, x) (th -^ y) rh
  with ta & ph <- masu (sg -, x) th rh
     = ta & ph -^ y
masu (sg -, x) (th -, .x) rh
  with ta & ph <- masu sg th rh
     = ta -, x & ph -, x
masu ((sg </ u \> t) -/ x) th rh =
  (masu sg (luth u -& th) rh /,\ ma t (ruth u -& th) rh)
  -/^ x

