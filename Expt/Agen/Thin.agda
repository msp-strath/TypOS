module Thin where

open import Basics

module THIN {X : Set} where

  infix 20 _<=_
  data _<=_ : Bwd X -> Bwd X -> Set where
    _-^_ : forall {xz yz}
      -> xz <= yz -> forall y -> xz      <= yz -, y
    _-,_ : forall {xz yz}
      -> xz <= yz -> forall x -> xz -, x <= yz -, x
    []   : [] <= []
  infixl 30 _-^_

  io : forall {xz} -> xz <= xz
  io {[]}      = []
  io {xz -, x} = io -, x
  
  no : forall {xz} -> [] <= xz
  no {[]}      = []
  no {xz -, x} = no -^ x

  data [_-&_]~_ : forall {xz yz zz}
    -> xz <= yz -> yz <= zz -> xz <= zz -> Set where
    _-^_ : forall {xz yz zz}
      {th : xz <= yz}{ph : yz <= zz}{ps : xz <= zz}
      -> [ th -& ph ]~ ps -> forall z
      -> [ th -& ph -^ z ]~ ps -^ z
    _-^,_ : forall {xz yz zz}
      {th : xz <= yz}{ph : yz <= zz}{ps : xz <= zz}
      -> [ th -& ph ]~ ps -> forall y
      -> [ th -^ y -& ph -, y ]~ ps -^ y
    _-,_ : forall {xz yz zz}
      {th : xz <= yz}{ph : yz <= zz}{ps : xz <= zz}
      -> [ th -& ph ]~ ps -> forall x
      -> [ th -, x -& ph -, x ]~ ps -, x
    [] : [ [] -& [] ]~ []

  tri : forall {xz yz zz}(th : xz <= yz)(ph : yz <= zz) ->
        < [ th -& ph ]~_ >
  tri th         (ph -^ y) with ! v <- tri th ph = ! v -^ y
  tri (th -^ .x) (ph -, x) with ! v <- tri th ph = ! v -^, x
  tri (th -, .x) (ph -, x) with ! v <- tri th ph = ! v -, x
  tri     []         []                          = !   []

  triQ : forall {xz yz zz}{th : xz <= yz}{ph : yz <= zz}
    (v w : < [ th -& ph ]~_ >) -> v ~ w
  triQ (! v -^ z)  (! w -^ .z)  with r~ <- triQ (! v) (! w) = r~
  triQ (! v -^, y) (! w -^, .y) with r~ <- triQ (! v) (! w) = r~
  triQ (! v -, x)  (! w -, .x)  with r~ <- triQ (! v) (! w) = r~
  triQ (!   [])    (!   [])     = r~

  _-&_ : forall {xz yz zz}(th : xz <= yz)(ph : yz <= zz) ->
     xz <= zz
  th -& ph = tri th ph .fst
  infixl 30 _-&_

  degio : forall {ga de}(th : ga <= de) -> [ th -& io ]~ th
  degio [] = []
  degio (th -^ x) = degio th -^, x
  degio (th -, x) = degio th -, x

  lio : forall {ga de}{th ph : ga <= de} ->
    [ io -& th ]~ ph -> th ~ ph
  lio (v -^ z) with r~ <- lio v = r~
  lio (v -, x) with r~ <- lio v = r~
  lio [] = r~

  rio : forall {ga de}{th ph : ga <= de} ->
    [ th -& io ]~ ph -> th ~ ph
  rio (v -^, y) with r~ <- rio v = r~
  rio (v -, x) with r~ <- rio v = r~
  rio [] = r~

  noBig : forall {xz x} -> xz -, x <= xz -> `0
  noBig (th -^ y) = noBig (io -^ _ -& th)
  noBig (th -, x) = noBig th

  asy : forall {xz yz}(th : xz <= yz)(ph : yz <= xz) ->
    (xz ~ yz) >< \ { r~ -> (th ~ io) * (ph ~ io) }
  asy (th -^ y) ph with r~ , _ <- asy th ((io -^ y) -& ph)
    | () <- noBig ph
  asy (th -, x) (ph -^ .x) with r~ , _ <- asy th ((io -^ x) -& ph)
    | () <- noBig ph
  asy (th -, x) (ph -, .x)
    with r~ , r~ , r~ <- asy th ph
       = r~ , r~ , r~
  asy [] [] = r~ , r~ , r~

  assoc03 : forall {xz0 xz1 xz2 xz3} ->
    {th01 : xz0 <= xz1}{th02 : xz0 <= xz2}
    {th13 : xz1 <= xz3}{th23 : xz2 <= xz3} ->
    < [ th01 -&_]~ th02 *: [_-& th23 ]~ th13 > ->
    < [ th01 -& th13 ]~_ *: [ th02 -& th23 ]~_ >
  assoc03 (v0 & v1 -^ z)
    with w0 & w1 <- assoc03 (v0 & v1) = w0 -^ z & w1 -^ z
  assoc03 (v0 -^ .y & v1 -^, y)
    with w0 & w1 <- assoc03 (v0 & v1) = w0 -^ y & w1 -^, y
  assoc03 (v0 -^, .x & v1 -, x)
    with w0 & w1 <- assoc03 (v0 & v1) = w0 -^, x & w1 -^, x
  assoc03 (v0 -, .x & v1 -, x)
    with w0 & w1 <- assoc03 (v0 & v1) = w0 -, x & w1 -, x
  assoc03 ([] & []) = [] & []

  assoc02 : forall {xz0 xz1 xz2 xz3} ->
    {th01 : xz0 <= xz1}{th03 : xz0 <= xz3}
    {th12 : xz1 <= xz2}{th23 : xz2 <= xz3} ->
    < [ th01 -&_]~ th03 *: [ th12 -& th23 ]~_ > ->
    < [ th01 -& th12 ]~_ *: [_-& th23 ]~ th03 >
  assoc02 {th01 = th01}{th12 = th12} (v0 & v1)
    with ! w <- tri th01 th12
       | v2 & v3 <- assoc03 (w & v1)
       | r~ <- triQ (! v0) (! v2)
       = w & v3

  assoc13 : forall {xz0 xz1 xz2 xz3} ->
    {th01 : xz0 <= xz1}{th03 : xz0 <= xz3}
    {th12 : xz1 <= xz2}{th23 : xz2 <= xz3} ->
    < [ th01 -& th12 ]~_ *: [_-& th23 ]~ th03 > ->
    < [ th01 -&_]~ th03 *: [ th12 -& th23 ]~_ >
  assoc13 {th12 = th12}{th23 = th23} (v0 & v1)
    with ! w <- tri th12 th23
       | v2 & v3 <- assoc03 (v0 & w)
       | r~ <- triQ (! v1) (! v3)
       = v2 & w

  infixl 12 _^:_
  _^:_ : (Bwd X -> Set) -> Bwd X -> Set
  P ^: de = < P *: _<= de >

  _:^_ : forall {P de} ->
    P ^: de -> forall x ->
    P ^: de -, x
  (p & th) :^ x = p & th -^ x

  eta^ : forall {P} -> [ P -:> P ^:_ ]
  eta^ p = p & io

  mu^ : forall {P} -> [ P ^:_ ^:_ -:> P ^:_ ]
  mu^ ((p & th) & ph) = p & th -& ph

  _=12>_ : forall {xz zz}
           {(th0 & ph0) (th1 & ph1) : < xz <=_ *: _<= zz >}
           {ps : xz <= zz} ->
           [ th0 -& ph0 ]~ ps ->
           [ th1 -& ph1 ]~ ps ->
           Set
  _=12>_ {_}{_}{th0 & ph0}{th1 & ph1} v0 v1 =
     < [ th0 -&_]~ th1 *: [_-& ph1 ]~ ph0 >

  all? : forall {ga de}(th : ga <= de) ->
    Maybe ((ga ~ de) >< \ { r~ -> th ~ io })
  all? (th -^ y) = ff , <>
  all? (th -, x) =
    maybe (\ { (r~ , r~) -> r~ , r~ }) (all? th)
  all? [] = tt , r~ , r~
