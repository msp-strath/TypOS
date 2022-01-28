open import Basics

module MangleActors
  (ActorVar Unknown : Nat -> Set)
  (ATOM : Set)
  where

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

module _
  {ga {- how many vars are really in scope -}}
  (rh : Env ga) where

  ma : forall
       {de0 -- support of source term
        de  -- how many binders in source term we're under
     }
    -> Src de0
    -> de0 <= de
    -> Trg ^: (ga <<< de)

  masu : forall
       {xi  -- scope of actor var
        de0 -- support of source term
        de  -- how many binders in source term we're under
       }
    -> xi S> de0
    -> de0 <= de
    -> (ga <<< xi) T>^ (ga <<< de)

  ma (vv only) th = v^ (no +^+ th)
  ma (aa (atom a)) th = a^ a
  ma (pp (s </ u \> t)) th =
    ma s (luth u -& th) ,^ ma t (ruth u -& th)
  ma (bb (kk t)) th = b^ (ma t (th -^ <>))
  ma (bb (ll t)) th = b^ (ma t (th -, <>))
  ma (mm (x & sg)) th = rh x //^ masu sg th

  masu [] th = is {- ga -} & io{-ga-} +^+ th {- 0<=de -}
  masu (sg -, x) (th -^ y)
    with ta & ph <- masu (sg -, x) th
       = ta & ph -^ y
  masu (sg -, x) (th -, .x)
    with ta & ph <- masu sg th
       = ta -, x & ph -, x
  masu ((sg </ u \> t) -/ x) th =
    (masu sg (luth u -& th) /,\ ma t (ruth u -& th))
    -/^ x
