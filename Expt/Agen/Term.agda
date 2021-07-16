module Term where

open import Basics
open import Thin
open import Cop
open import Pair
open import Bind

open THIN {`1}
open COP  {`1}
open PAIR {`1}
open BIND {`1}

Nat = Bwd `1

module TERM (M : Nat -> Set)(A : Set) where

  data _%>_ : Nat -> Nat -> Set
  data Tm (ga : Nat) : Set where
    vv : Only <> ga      -> Tm ga
    aa : Atom A ga       -> Tm ga
    pp : (Tm </\> Tm) ga -> Tm ga
    bb : (<> |- Tm) ga   -> Tm ga
    mm : < M *: _%> ga > -> Tm ga

  Term = Tm ^:_

  infix 20 _%>_
  infixl 30 _-/_
  data _%>_ where
    []   : [] %> []
    _-,_ : forall {ga de} -> ga %> de -> forall x -> ga -, x %> de -, x
    _-/_ : forall {ga de} -> (ga %>_ </\> Tm) de -> forall x -> ga -, x %> de

  is : forall {ga} -> ga %> ga
  is {[]} = []
  is {ga -, x} = is -, x

  is? : forall {ga de}(sg : ga %> de) -> Maybe ((ga ~ de) >< \ { r~ -> sg ~ is })
  is? [] = tt , r~ , r~
  is? (sg -, x) with is? sg
  ... | tt , r~ , r~ = tt , r~ , r~
  ... | ff , <> = ff , <>
  is? (_ -/ _) = ff , <>

  coverSub : forall {ga0 ga ga1}{th0 : ga0 <= ga}{th1 : ga1 <= ga}{de}
        -> th0 /u\ th1 -> ga %> de
        -> < _<= de *: ga0 %>_ > >< \ (ph0 & _)
        -> < _<= de *: ga1 %>_ > >< \ (ph1 & _)
        -> ph0 /u\ ph1
  coverSub (u -,^ x) (sg -, .x)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
       = _ & sg0 -, x , _ & sg1 , u' -,^ x
  coverSub (u -,^ x) ((sg </ v \> t) -/ .x)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
       | ! ! u1 , u2 <- rotateR (swapu u') v
       = _ & (sg0 </ u2 \> t) -/ x , _ & sg1 , swapu u1
  coverSub (u -^, y) (sg -, .y)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
       = _ & sg0 , _ & sg1 -, y , u' -^, y
  coverSub (u -^, y) ((sg </ v \> t) -/ .y)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
       | ! ! u1 , u2 <- rotateR u' v
       = _ & sg0 , _ & (sg1 </ u2 \> t) -/ y , u1
  coverSub (u -, z) (sg -, .z)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
       = _ & sg0 -, z , _ & sg1 -, z , u' -, z
  coverSub (u -, z) ((sg </ v \> t) -/ .z)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
       | ! ! ! ! w0 , w , w1 <- distR u' v
       = _ & (sg0 </ w0 \> t) -/ z , _ & (sg1 </ w1 \> t) -/ z , w
  coverSub [] [] = (! ! []) , (! ! []) , []

  infix 20 _<%_ _<%^_
  _<%^_ : forall {ga de xi} ->
    ga <= de -> de %>_ ^: xi -> (ga %>_ ^: xi) + (ga <= xi)
  _<%_ : forall {ga de xi} ->
    ga <= de -> de %> xi -> (ga %>_ ^: xi) + (ga <= xi)
  th <%^ (sg & ph) with th <% sg
  ... | ff , ro = ff , mu^ (ro & ph)
  ... | tt , ps = tt , ps -& ph
  th -^ y <% sg -, .y with th <% sg
  ... | ff , ro = ff , ro :^ y
  ... | tt , ps = tt , ps -^ y
  th -^ y <% (sg </ u \> _) -/ .y with th <% sg
  ... | ff , ro = ff , mu^ (ro & luth u)
  ... | tt , ps = tt , ps -& luth u
  th -, x <% sg -, .x with th <% sg
  ... | ff , ro & ph = ff , ro -, x & ph -, x
  ... | tt , ps = tt , ps -, x
  th -, x <% (sg </ u \> t) -/ .x with th <% sg
  ... | ff , ro with ta & ps <- mu^ (ro & luth u) /,\ (t & ruth u) =
    ff , ta -/ x & ps
  ... | tt , ps with ta & ps <- is & (ps -& luth u) /,\ (t & ruth u) =
    ff , ta -/ x & ps
  [] <% [] = tt , []

  Var = [] -, <> <=_

  v^ : [ Var -:> Term ]
  v^ th = vv only & th

  a^ : A -> [ Term ]
  a^ a = aa (atom a) & no

  _,^_ : [ Term -:> Term -:> Term ]
  s ,^ t with p & th <- s /,\ t = pp p & th

  b^ : [ _-, <> - Term -:> Term ]
  b^ t with b & th <- <> \\ t = bb b & th

  m^ : forall {ga de} ->
       M ga -> ga %>_ ^: de -> Term de
  m^ m (sg & th) = mm (m & sg) & th

  act?  : forall {ga de} -> Tm ga -> ga %> de -> Tm de
  act  : forall {ga de} -> Tm ga -> ga %> de -> Tm de
  _%%?_ : forall {ga de xi} -> ga %> de -> de %> xi -> ga %> xi
  _%%_ : forall {ga de xi} -> ga %> de -> de %> xi -> ga %> xi
  act? t sg with is? sg
  act? t sg | ff , _ = act t sg
  act? t .is | tt , r~ , r~ = t
  act (vv only) ([] -, .<>) = vv only
  act (vv only) (([] </ u \> t) -/ .<>) with r~ , r~ , r~ <- allRight u = t
  act (aa (atom a)) [] = aa (atom a)
  act (pp (s </ u \> t)) sg
    with _ & sg0 , _ & sg1 , v <- coverSub u sg
       = pp (act? s sg0 </ v \> act? t sg1)
  act (bb (kk t)) sg = bb (kk (act t sg))
  act (bb (ll t)) sg = bb (ll (act t (sg -, _)))
  act (mm (m & ro)) sg = mm (m & (ro %% sg))
  ro %%? sg with is? ro | is? sg
  (ro %%? sg) | ff , x | ff , y = ro %% sg
  (ro %%? .is) | ff , x | tt , r~ , r~ = ro
  (.is %%? sg) | tt , r~ , r~ | c , y = sg
  [] %% [] = []
  (ro -, x) %% (sg -, .x) = (ro %% sg) -, x
  (ro -, x) %% ((sg </ u \> t) -/ .x) = ((ro %%? sg) </ u \> t) -/ x
  ((ro </ u \> t) -/ x) %% sg
    with _ & sg0 , _ & sg1 , v <- coverSub u sg
       = ((ro %%? sg0) </ v \> act? t sg1) -/ x
