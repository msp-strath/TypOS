module Cop where

open import Basics
open import Thin

module COP {X} where

  open THIN {X}

  data _/u\_ : forall {xz yz zz} -> xz <= yz -> zz <= yz -> Set where
    _-,^_ : forall {xz yz zz}{th : xz <= yz}{ph : zz <= yz}
      -> th /u\ ph -> forall x
      -> th -, x /u\ ph -^ x
    _-^,_ : forall {xz yz zz}{th : xz <= yz}{ph : zz <= yz}
      -> th /u\ ph -> forall y
      -> th -^ y /u\ ph -, y
    _-,_ : forall {xz yz zz}{th : xz <= yz}{ph : zz <= yz}
      -> th /u\ ph -> forall z
      -> th -, z /u\ ph -, z
    []   : [] /u\ []
  infix 20 _/u\_

  luth : forall {xz yz zz}
    {th : xz <= yz}{ph : zz <= yz}
    -> th /u\ ph -> xz <= yz
  luth {th = th} u = th

  ruth : forall {xz yz zz}
    {th : xz <= yz}{ph : zz <= yz}
    -> th /u\ ph -> zz <= yz
  ruth {ph = ph} u = ph

  copI : forall {xz yz zz}{th : xz <= yz}{ph : zz <= yz}
    (u u' : th /u\ ph) -> u ~ u'
  copI (u -,^ x) (u' -,^ .x) with r~ <- copI u u' = r~
  copI (u -^, y) (u' -^, .y) with r~ <- copI u u' = r~
  copI (u -, z) (u' -, .z) with r~ <- copI u u' = r~
  copI [] [] = r~

  Cop : forall {xz yz zz}(th : xz <= yz)(ph : zz <= yz) -> Set
  Cop {xz}{yz}{zz} th ph =
        _ >< \ uz -> xz <= uz >< \ th' -> zz <= uz >< \ ph' ->
        < [ th' -&_]~ th *: [ ph' -&_]~ ph >
        
  cop : forall {xz yz zz}(th : xz <= yz)(ph : zz <= yz) ->
    Cop th ph >< \ (! th' , ph' , _) -> th' /u\ ph'
  cop (th -^ z) (ph -^ .z)
    with (! ! ! v       & w     ) , u       <- cop th ph
       = (! ! ! v -^ z  & w -^ z) , u
  cop (th -^ y) (ph -, .y)
    with (! ! ! v       & w     ) , u       <- cop th ph
       = (! ! ! v -^, y & w -, y) , u -^, y
  cop (th -, x) (ph -^ .x)
    with (! ! ! v      & w      ) , u       <- cop th ph
       = (! ! ! v -, x & w -^, x) , u -,^ x
  cop (th -, z) (ph -, .z)
    with (! ! ! v      & w     )  , u       <- cop th ph
       = (! ! ! v -, z & w -, z)  , u -, z
  cop     []        []
       = (! ! !   []   &   []  )  ,   []

  copU : forall {xz yz zz}{th : xz <= yz}{ph : zz <= yz}
    -> ((! th0 , ph0 , ps0 , _ , _) : Cop th ph)
    -> th0 /u\ ph0
    -> ((! th1 , ph1 , ps1 , _ , _) : Cop th ph)
    -> < [ th0 -&_]~ th1 *: [_-& ps1 ]~ ps0 *: [ ph0 -&_]~ ph1 >
  copU (! ! ! v0 -^ z & w0 -^ .z) u (! ! ! v1 -^ .z & w1 -^ .z)
    with ! a      , b       , c <- copU (! ! ! v0 & w0) u (! ! ! v1 & w1)
    =    ! a      , b -^ z  , c
  copU (! ! ! v0 -^ z & w0 -^ .z) u (! ! ! v1 -^, .z & w1 -^, .z)
    with ! a , b      , c <- copU (! ! ! v0 & w0) u (! ! ! v1 & w1)
    =    ! a -^ z , b -^, z , c -^ z
  copU (! ! ! v0 -^, y & w0 -, .y) (u -^, .y) (! ! ! v1 -^, .y & w1 -, .y)
    with ! a       , b      , c <- copU (! ! ! v0 & w0) u (! ! ! v1 & w1)
    =    ! a -^, y , b -, y , c -, y
  copU (! ! ! v0 -, x & w0 -^, .x) (u -,^ .x) (! ! ! v1 -, .x & w1 -^, .x)
    with ! a       , b      , c <- copU (! ! ! v0 & w0) u (! ! ! v1 & w1)
    =    ! a -, x  , b -, x , c -^, x
  copU (! ! ! v0 -, x & w0 -, .x)  (u -, .x)  (! ! ! v1 -, .x & w1 -, .x)
    with ! a       , b      , c <- copU (! ! ! v0 & w0) u (! ! ! v1 & w1)
    =    ! a -, x  , b -, x , c -, x
  copU (! ! ! [] & []) [] (! ! ! [] & []) = ! [] , [] , []

  copQ : forall {ga0 ga1 ga de}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
           (u : th0 /u\ th1)(ps : ga <= de) ->
    let ph0 , v0 = tri th0 ps in
    let ph1 , v1 = tri th1 ps in
    cop ph0 ph1 ~ ((! ! ! v0 & v1) , u)
  copQ {th0 = th0}{th1 = th1 } u ps
    with ph0 , v0 <- tri th0 ps
       | ph1 , v1 <- tri th1 ps
       | c@(ga' , ch0 , ch1 , ch2 , v2 , v3) , u' <- cop ph0 ph1
       | ps0 , w0 , w1 , w2 <- copU c u' (! ! ! v0 & v1)
       | ps1 , w3 , w4 , w5 <- copU (! ! ! v0 & v1) u c
       | r~ , r~ , r~ <- asy ps0 ps1
       | r~ <- rio w0
       | r~ <- lio w1
       | r~ <- rio w2
       | r~ <- copI u u'
       | r~ , r~ <- triQ (! v0) (! v2)
       | r~ , r~ <- triQ (! v1) (! v3)
       = r~

  llu : forall {ga} -> io {ga} /u\ no
  llu {[]}      = []
  llu {ga -, x} = llu -,^ x

  rru : forall {ga} -> no {ga} /u\ io
  rru {[]}      = []
  rru {ga -, x} = rru -^, x

  allRight : forall {ga de}{th : [] <= de}{ph : ga <= de}
    -> th /u\ ph -> (ga ~ de) >< \ { r~ -> (th ~ no) * (ph ~ io) }
  allRight (u -^, y) with r~ , r~ , r~ <- allRight u = r~ , r~ , r~
  allRight [] = r~ , r~ , r~
           
  rotateR : forall {ga00 ga0 ga01 ga1 ga}{th00 : ga00 <= ga0}{th01 : ga01 <= ga0}
    {th0 : ga0 <= ga}{th1 : ga1 <= ga}
    (u0 : th00 /u\ th01)(u : th0 /u\ th1)
    ->
    < ga01 <=_ *: _<= ga *: ga1 <=_ > >< \ (! ph01 , ph , ph1)  ->
    < [ th00 -& th0 ]~_ > >< \ (ph00 , v00) ->
    ph00 /u\ ph * ph01 /u\ ph1
  rotateR u0 (u -^, y) with ! (! v) , w , w1 <- rotateR u0 u
    = ! (! v -^ y) , w -^, y , w1 -^, y
  rotateR (u0 -,^ .x) (u -,^ x) with ! (! v) , w , w1 <- rotateR u0 u
    = ! (! v -, x) , w -,^ x , w1
  rotateR (u0 -^, .x) (u -,^ x) with ! (! v) , w , w1 <- rotateR u0 u
    = ! (! v -^, x) , w -^, x , w1 -,^ x
  rotateR (u0 -, .x) (u -,^ x) with ! (! v) , w , w1 <- rotateR u0 u
    = ! (! v -, x) , w -, x , w1 -,^ x
  rotateR (u0 -,^ .z) (u -, z) with ! (! v) , w , w1 <- rotateR u0 u
    = ! (! v -, z) , w -, z , w1 -^, z
  rotateR (u0 -^, .z) (u -, z) with ! (! v) , w , w1 <- rotateR u0 u
    = ! (! v -^, z) , w -^, z , w1 -, z
  rotateR (u0 -, .z) (u -, z) with ! (! v) , w , w1 <- rotateR u0 u
    = ! (! v -, z) , w -, z , w1 -, z
  rotateR [] [] = ! (! []) , [] , []

  swapu : forall {ga0 ga ga1}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
       -> th0 /u\ th1 -> th1 /u\ th0
  swapu (u -,^ x) = swapu u -^, x
  swapu (u -^, y) = swapu u -,^ y
  swapu (u -, z) = swapu u -, z
  swapu [] = []

  -- is there a prettier way to see this?
  -- missing pullbacks?
  distR : forall {ga00 ga0 ga01 ga ga1}
    {th00 : ga00 <= ga0}{th01 : ga01 <= ga0}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
    (u0 : th00 /u\ th01)(u : th0 /u\ th1)
    -> < ga00 <=_ *: ga1 <=_ > >< \ (th10 & ph10)
    -> < ga01 <=_ *: ga1 <=_ > >< \ (th11 & ph11)
    -> < [ ph10 -&_]~ th1 > >< \ (ps0 , _)
    -> < [ ph11 -&_]~ th1 > >< \ (ps1 , _)
    -> th10 /u\ ph10 * ps0 /u\ ps1 * th11 /u\ ph11
  distR u0 (u -^, y)
    with ! ! (! v0) , (! v1) , w0 , w , w1 <- distR u0 u
       = ! ! (! v0 -, y) , (! v1 -, y) , w0 -^, y , w -, y , w1 -^, y
  distR (u0 -,^ .x) (u -,^ x)
    with ! ! (! v0) , (! v1) , w0 , w , w1 <- distR u0 u
       = ! ! (! v0 -^, x) , (! v1 -^ x) , w0 -,^ x , w -,^ x , w1
  distR (u0 -^, .x) (u -,^ x)
    with ! ! (! v0) , (! v1) , w0 , w , w1 <- distR u0 u
       = ! ! (! v0 -^ x) , (! v1 -^, x) , w0 , w -^, x , w1 -,^ x
  distR (u0 -, .x) (u -,^ x)
    with ! ! (! v0) , (! v1) , w0 , w , w1 <- distR u0 u
       = ! ! (! v0 -^, x) , (! v1 -^, x) , w0 -,^ x , w -, x , w1 -,^ x
  distR (u0 -,^ .z) (u -, z)
    with ! ! (! v0) , (! v1) , w0 , w , w1 <- distR u0 u
       = ! ! (! v0 -, z) , (! v1 -, z) , w0 -, z , w -, z , w1 -^, z
  distR (u0 -^, .z) (u -, z)
    with ! ! (! v0) , (! v1) , w0 , w , w1 <- distR u0 u
       = ! ! (! v0 -, z) , (! v1 -, z) , w0 -^, z , w -, z , w1 -, z
  distR (u0 -, .z) (u -, z)
    with ! ! (! v0) , (! v1) , w0 , w , w1 <- distR u0 u
       = ! ! (! v0 -, z) , (! v1 -, z) , w0 -, z , w -, z , w1 -, z
  distR [] [] = ! ! (! []) , (! []) , [] , [] , []

  distR' : forall {ga00 ga0 ga01 ga ga1}
    {th00 : ga00 <= ga0}{th01 : ga01 <= ga0}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
    (u0 : th00 /u\ th01)(u : th0 /u\ th1)
    -> < ga00 <=_ *: ga1 <=_ > >< \ (th10 & ph10)
    -> < ga01 <=_ *: ga1 <=_ > >< \ (th11 & ph11)
    -> < [ ph10 -&_]~ th1 > >< \ (ps0 , _)
    -> < [ ph11 -&_]~ th1 > >< \ (ps1 , _)
    -> th10 /u\ ph10 * ps0 /u\ ps1 * th11 /u\ ph11
  distR' {th0 = th0}{th1 = th1} u0 u
    with ph0 , v0 <- tri (luth u0) (luth u)
       | ph1 , v1 <- tri (ruth u0) (luth u)
       | (! ! ! ps0 , a0 , b0) , w0 <- cop ph0 (ruth u)
       | (! ! ! ps1 , a1 , b1) , w1 <- cop ph1 (ruth u)
       | (! ! ! ps , a , b) , w <- cop ps0 ps1
       | c0 & d0 <- assoc02 (a0 & a)
       | c1 & d1 <- assoc02 (a1 & b)
       | ! e , f , g <- copU (! ! ! v0 & v1) u0 (! ! ! d0 & d1)
       | k & l <- assoc02 (b1 & b)
       | ps' , h , i , j <- copU (! ! ! degio th0 & degio th1) u (! ! ! f & l)
       | r~ , r~ , r~ <- asy ps ps'
       | r~ <- rio a
       | r~ <- rio b
       = ! ! (! b0) , (! b1) , w0 , w , w1

{-
  distRswap : forall {ga00 ga0 ga01 ga ga1}
    {th00 : ga00 <= ga0}{th01 : ga01 <= ga0}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
    (u0 : th00 /u\ th01)(u : th0 /u\ th1) ->
    let ! ! (! b0) , (! b1) , w0 , w , w1 = distR' u0 u in
    distR' (swapu u0) u ~ (! ! (! b1) , (! b0) , w1 , swapu w , w0)
  distRswap {th0 = th0}{th1 = th1} u0 u
    with ph0 , v0 <- tri (luth u0) (luth u)
       | ph1 , v1 <- tri (ruth u0) (luth u)
       = {!!}
-}
