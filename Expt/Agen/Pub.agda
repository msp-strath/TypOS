module Pub where

open import Basics
open import Thin

module PUB {X : Set} where
  open THIN {X}

  Squ : forall {wz zz}((th' & th) (ph' & ph) : < wz <=_ *: _<= zz >) -> Set
  Squ (! th' , th) (! ph' , ph) = < [ th' -& th ]~_ *: [ ph' -& ph ]~_ >
{-
      wz  wz-----th'---->o       wz-----th'---->o 
       |                 |        |`-,          | 
  Squ ph'                th   =  ph'  `-,       th  
       |                 |        |      `-,    | 
       v                 v        v         --->v 
       o-----ph'---->zz  zz       o-----ph'---->zz
-}
  data Pub : forall {wz zz}(ths phs : < wz <=_ *: _<= zz >) -> Set where
    _-^_ : forall {wz zz}{(th' & th) (ph' & ph) : < wz <=_ *: _<= zz >}
        -> Pub (th' & th) (ph' & ph) -> forall z
        -> Pub (th' & th -^ z) (ph' & ph -^ z)
    _-^,_ : forall {wz zz}{(th' & th) (ph' & ph) : < wz <=_ *: _<= zz >}
        -> Pub (th' & th) (ph' & ph) -> forall y
        -> Pub (th' & th -^ y) (ph' -^ y & ph -, y)
    _-,^_ : forall {wz zz}{(th' & th) (ph' & ph) : < wz <=_ *: _<= zz >}
        -> Pub (th' & th) (ph' & ph) -> forall x
        -> Pub (th' -^ x & th -, x) (ph' & ph -^ x)
    _-,_ : forall {wz zz}{(th' & th) (ph' & ph) : < wz <=_ *: _<= zz >}
        -> Pub (th' & th) (ph' & ph) -> forall z
        -> Pub (th' -, z & th -, z) (ph' -, z & ph -, z)
    []   : Pub ([] & []) ([] & [])
    
  pub : forall {xz yz zz}(th : xz <= zz)(ph : yz <= zz) ->
    < _<= xz *: _<= yz > >< \ (th' & ph') ->
    Squ (th' & th) (ph' & ph) * Pub (th' & th) (ph' & ph)
  pub (th -^ z) (ph -^ .z)
    with ! v & w , p <- pub th ph
       = ! v -^ z & w -^ z , p -^ z
  pub (th -^ y) (ph -, .y)
    with ! v & w , p <- pub th ph
       = ! v -^ y & w -^, y , p -^, y
  pub (th -, x) (ph -^ .x)
    with ! v & w , p <- pub th ph
       = ! v -^, x & w -^ x , p -,^ x
  pub (th -, z) (ph -, .z)
    with ! v & w , p <- pub th ph
       = ! v -, z & w -, z , p -, z
  pub [] [] = ! [] & [] , []

  pubU : forall {xz yz zz}{th : xz <= zz}{ph : yz <= zz}
    -> ((th0 & ph0 , _) (th1 & ph1 , _) : < _<= xz *: _<= yz > >< \ (th' & ph')
          -> Squ (th' & th) (ph' & ph))
    -> Pub (th0 & th) (ph0 & ph)
    -> < [_-& th0 ]~ th1 *: [_-& ph0 ]~ ph1 >
  pubU (! v0 -^ .z & w0 -^ .z) (! v1 -^ .z & w1 -^ .z) (p -^ z) =
    pubU (! v0 & w0) (! v1 & w1) p
  pubU (! v0 -^ .y & w0 -^, .y) (! v1 -^ .y & w1 -^, .y) (p -^, y)
    with v & w <- pubU (! v0 & w0) (! v1 & w1) p = v & w -^ y
  pubU (! v0 -^, .x & w0 -^ .x) (! v1 -^, .x & w1 -^ .x) (p -,^ x)
    with v & w <- pubU (! v0 & w0) (! v1 & w1) p = v -^ x & w
  pubU (_ & ((v0 -^, .x) , w0 -^ .x)) (_ & ((v1 -, .x) , ())) (p -,^ x)
  pubU (! v0 -, .z & w0 -, .z) (! v1 -^, .z & w1 -^, .z) (p -, z)
    with v & w <- pubU (! v0 & w0) (! v1 & w1) p = v -^, z & w -^, z
  pubU (! v0 -, .z & w0 -, .z) (! v1 -, .z & w1 -, .z) (p -, z)
    with v & w <- pubU (! v0 & w0) (! v1 & w1) p = v -, z & w -, z
  pubU (! [] & []) (! [] & []) [] = [] & []

  widen : forall {wz zz}(ths : < wz <=_ *: _<= zz >) ->
          < Squ ths *: Pub ths >
  widen (th' & th -^ y)
    with (v & w) & p <- widen (th' & th)
    = (v -^ y & w -^, y) & p -^, y
  widen (th' -^ .x & th -, x)
    with (v & w) & p <- widen (th' & th)
    = (v -^, x & w -^ x) & p -,^ x
  widen (th' -, .x & th -, x)
    with (v & w) & p <- widen (th' & th)
    = (v -, x & w -, x) & p -, x
  widen ([] & []) = ([] & []) & []

  widenU : forall {wz zz}(ths : < wz <=_ *: _<= zz >) ->
    let (ps , v , w) & p = widen ths in
    {phs@(ph0 & ph1) : < wz <=_ *: _<= zz >} ->
    Pub ths phs ->
    (w' : [ ph0 -& ph1 ]~ ps) ->
    w' =12> w
  widenU (th0 & th1 -^ z) (p -^ z) (w' -^ .z)
    with a & b <- widenU (th0 & th1) p w' = a -^ z & b -^, z
  widenU (th0 & th1 -^ y) (p -^, y) (w' -^, .y)
    with a & b <- widenU (th0 & th1) p w' = a -^, y & b -, y
  widenU (th0 -^ x & th1 -, x) (p -,^ x) (w' -^ .x)
    with a & b <- widenU (th0 & th1) p w' = a & b -^ x
  widenU (th0 -, z & th1 -, .z) (p -, z) (w' -, .z)
    with a & b <- widenU (th0 & th1) p w' = a -, z & b -, z
  widenU ([] & []) [] [] = [] & []
    
  thicken? : forall {xz yz zz}(ph : yz <= zz)(ps : xz <= zz) ->
    Maybe < [_-& ph ]~ ps >
  thicken? ph ps with pub ph ps
  ... | ph' & ps' , v & w , p with all? ps'
  ... | ff , <> = ff , <>
  ... | tt , r~ , r~
    with r~ <- lio w
      = tt , ! v

