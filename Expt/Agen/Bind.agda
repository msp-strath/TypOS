module Bind where

open import Basics
open import Thin

module BIND {X : Set} where
  open THIN {X}

  data _|-_ (x : X)(P : Bwd X -> Set)(ga : Bwd X) : Set where
    kk : P ga -> (x |- P) ga
    ll : P (ga -, x) -> (x |- P) ga

  _\\_ : {P : Bwd X -> Set}(x : X) ->
         [ ((_-, x) - (P ^:_)) -:> (x |- P) ^:_ ]
  x \\ (p & th -^ .x) = kk p & th
  x \\ (p & th -, .x) = ll p & th

  data Only (x : X) : Bwd X -> Set where
    only : Only x ([] -, x)
