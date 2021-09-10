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

  infix 20 _%>_
  infixl 30 _-/_
  data _%>_ where
    []   : [] %> []
    _-,_ : forall {ga de} -> ga %> de -> forall x -> ga -, x %> de -, x
    _-/_ : forall {ga de} -> (ga %>_ </\> Tm) de -> forall x -> ga -, x %> de

  supp : forall {ga} -> Tm ga -> Nat
  supp {ga} t = ga

  Term = Tm ^:_

  _%>^_ : Nat -> Nat -> Set
  ga %>^ de = (ga %>_) ^: de


  is : forall {ga} -> ga %> ga
  is {[]} = []
  is {ga -, x} = is -, x

  is? : forall {ga de}(sg : ga %> de) -> Maybe ((ga ~ de) >< \ { r~ -> sg ~ is })
  is? [] = tt , r~ , r~
  is? (sg -, x) with is? sg
  ... | tt , r~ , r~ = tt , r~ , r~
  ... | ff , <> = ff , <>
  is? (_ -/ _) = ff , <>

  is?is : forall {ga} -> is? (is {ga}) ~ (tt , r~ , r~)
  is?is {[]} = r~
  is?is {ga -, x} with is? (is {ga}) | is?is {ga}
  ... | _ | r~ = r~

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
    with ! ! u1 , u2 <- rotateR (swapu u') v
       = _ & (sg0 </ u2 \> t) -/ x , _ & sg1 , swapu u1
  coverSub (u -^, y) (sg -, .y)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
       = _ & sg0 , _ & sg1 -, y , u' -^, y
  coverSub (u -^, y) ((sg </ v \> t) -/ .y)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
    with ! ! u1 , u2 <- rotateR u' v
       = _ & sg0 , _ & (sg1 </ u2 \> t) -/ y , u1
  coverSub (u -, z) (sg -, .z)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
       = _ & sg0 -, z , _ & sg1 -, z , u' -, z
  coverSub (u -, z) ((sg </ v \> t) -/ .z)
    with ph0 & sg0 , ph1 & sg1 , u' <- coverSub u sg
    with ! ! ! ! w0 , w , w1 <- distR u' v
       = _ & (sg0 </ w0 \> t) -/ z , _ & (sg1 </ w1 \> t) -/ z , w
  coverSub [] [] = (! ! []) , (! ! []) , []

  coverIs : forall {ga0 ga ga1}{th0 : ga0 <= ga}{th1 : ga1 <= ga}(u : th0 /u\ th1)
         -> coverSub u is ~ ((! ! is) , (! ! is) , u)
  coverIs (u -,^ x) rewrite coverIs u = r~
  coverIs (u -^, y) rewrite coverIs u = r~
  coverIs (u -, z) rewrite coverIs u = r~
  coverIs [] = r~

{-
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
-}

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
       M ga -> ga %>^ de -> Term de
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
  act (mm (m & ro)) sg = mm (m & (ro %%? sg))
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

  act?is : forall {ga}(t : Tm ga) -> act? t is ~ t
  act?is {ga} t with is? (is {ga}) | is?is {ga}
  ... | _ | r~ = r~

  lis : forall {ga de}(sg : ga %> de) -> (is %%? sg) ~ sg
  lis {ga}{de} sg with is? (is {ga}) | is?is {ga}
  ... | _ | r~ = r~

  lis' : forall {ga de}(sg : ga %> de) -> (is %% sg) ~ sg
  lis' [] = r~
  lis' (sg -, x) rewrite lis' sg = r~
  lis' ((sg </ u \> t) -/ x) rewrite lis sg = r~

  ris : forall {ga de}(sg : ga %> de) -> (sg %%? is) ~ sg
  ris {ga}{de} sg with is? sg | is? (is {de}) | is?is {de}
  ris {ga} {de} sg | ff , _  | _ | r~ = r~
  ris {ga} {de} sg | tt , r~ , r~ | _ | r~ = r~

  ris' : forall {ga de}(sg : ga %> de) -> (sg %% is) ~ sg
  ris' [] = r~
  ris' (sg -, x) rewrite ris' sg = r~
  ris' ((sg </ u \> t) -/ x)
    rewrite coverIs u
          | ris sg
          | act?is t = r~

  opti : forall {ga de xi}(ro : ga %> de)(sg : de %> xi) ->
         (ro %%? sg) ~ (ro %% sg)
  opti {ga}{de}{xi} ro sg with is? ro | is? sg
  opti {ga} {de} {xi} ro sg | ff , z | ff , y = r~
  opti {ga} {de} {xi} ro sg | ff , z | tt , r~ , r~
    rewrite ris' ro = r~
  opti {ga} {de} {xi} ro sg | tt , r~ , r~ | c , y
    rewrite lis' sg = r~

  sbstSel : forall {ga0 ga de} -> ga0 <= ga -> ga %> de -> ga0 %>^ de
  sbstSel [] [] = [] & []
  sbstSel (th -^ .x) (sg -, x) = sbstSel th sg :^ x
  sbstSel (th -, .x) (sg -, x) =
    let (ta & ph) = sbstSel th sg in ta -, x & ph -, x
  sbstSel (th -^ .x) ((sg </ u \> t) -/ x) = mu^ (sbstSel th sg & luth u)
  sbstSel (th -, .x) ((sg </ u \> t) -/ x) =
    (_-/ x) $^ ((mu^ (sbstSel th sg & luth u)) /,\ t & ruth u)


  _//^_ : forall {ga de} -> Term ga -> ga %>^ de -> Term de
  (t & th) //^ (sg & ph) =
    let (sg' & ph') = sbstSel th sg in act t sg' & ph' -& ph

  _<%<_ : forall {ga0 ga1 de0 de1} ->
          ga0 %> de0 -> ga1 %> de1 -> (ga0 <<< ga1) %> (de0 <<< de1)
  sg <%< [] = sg
  sg <%< (ta -, x) = (sg <%< ta) -, x
  sg <%< ((ta </ u \> t) -/ x) with ! ! u' <- tensor llu u
    rewrite []<<< supp t = ((sg <%< ta) </ u' \> t) -/ x


{-
  coverSwap : forall {ga0 ga ga1}{th0 : ga0 <= ga}{th1 : ga1 <= ga}(u : th0 /u\ th1)
              {de}(sg : ga %> de) ->
              let _ & sg0 , _ & sg1 , v = coverSub u sg in
              coverSub (swapu u) sg ~ (_ & sg1 , _ & sg0 , swapu v)
  coverSwap (u -,^ x) (sg -, .x) rewrite coverSwap u sg = r~
  coverSwap (u -,^ x) ((sg </ v \> t) -/ .x)
    with coverSub u sg | coverSwap u sg
  ... | _ & sg0 , _ & sg1 , w | q
    with coverSub (swapu u) sg
  coverSwap (u -,^ x) ((sg </ v \> t) -/ .x) | _ & ta1 , _ & ta0 , w | r~ | _
    with ! ! y , z <- rotateR (swapu w) v
    rewrite copI (swapu (swapu y)) y
    = r~
  coverSwap (u -^, y) (sg -, .y) rewrite coverSwap u sg = r~
  coverSwap (u -^, y) ((sg </ v \> t) -/ .y) 
    with coverSub u sg | coverSwap u sg
  ... | _ & sg0 , _ & sg1 , w | q
    with coverSub (swapu u) sg
  coverSwap (u -^, y) ((sg </ v \> t) -/ .y) | _ & ta1 , _ & ta0 , w | r~ | _
    rewrite copI (swapu (swapu w)) w
    = r~
  coverSwap (u -, z) (sg -, .z) rewrite coverSwap u sg = r~
  coverSwap (u -, z) ((sg </ v \> t) -/ .z) 
    with coverSub u sg | coverSwap u sg
  ... | _ & sg0 , _ & sg1 , w | q with coverSub (swapu u) sg
  coverSwap (u -, z) ((sg </ v \> t) -/ .z) | _ & ta1 , _ & ta0 , w | r~ | _ = {!!}
  coverSwap [] [] = r~
-}
{-
  cover%% : forall {ga0 ga ga1 de}{th0 : ga0 <= ga}{th1 : ga1 <= ga}
    (u : th0 /u\ th1)(sg : ga %> de){xi}(ta : de %> xi)
    ->
    let _ & sg0 , _ & sg1 , v = coverSub u sg in
    let _ & ta0 , _ & ta1 , w = coverSub v ta in
    coverSub u (sg %% ta) ~ (_ & (sg0 %% ta0) , _ & (sg1 %% ta1) , w)
  cover%% (u -,^ x) (sg -, .x) (ta -, .x) rewrite cover%% u sg ta = r~
  cover%% (u -,^ x) (sg -, .x) ((ta </ u' \> t) -/ .x)
    with ih <- cover%% u sg ta
       | _ & sg0 , _ & sg1 , v <- coverSub u sg
       | _ & ta0 , _ & ta1 , w <- coverSub v ta
    rewrite opti sg ta | opti sg0 ta0 | opti sg1 ta1 | ih
       = r~
  cover%% (u -,^ x) ((sg </ u' \> t) -/ .x) ta
    with _ & ta0 , _ & ta1 , u'' <- coverSub u' ta
       | ih <- cover%% u sg ta0
       | _ & sg0 , _ & sg1 , v <- coverSub u sg
       | _ & ta00 , _ & ta01 , w <- coverSub v ta0
    rewrite opti sg ta0 | ih
       = {!!}
  cover%% (u COP.-^, y) (sg -, .y) (ta -, .y) = {!!}
  cover%% (u COP.-^, y) (sg -, .y) (x -/ .y) = {!!}
  cover%% (u COP.-^, y) (x -/ .y) [] = {!!}
  cover%% (u COP.-^, y) (x -/ .y) (ta -, x₁) = {!!}
  cover%% (u COP.-^, y) (x -/ .y) (x₁ -/ x₂) = {!!}
  cover%% (u COP.-, z) (sg -, .z) (ta -, .z) = {!!}
  cover%% (u COP.-, z) (sg -, .z) (x -/ .z) = {!!}
  cover%% (u COP.-, z) (x -/ .z) [] = {!!}
  cover%% (u COP.-, z) (x -/ .z) (ta -, x₁) = {!!}
  cover%% (u COP.-, z) (x -/ .z) (x₁ -/ x₂) = {!!}
  cover%% COP.[] [] [] = {!!}
-}

{-
  asso : forall {ga de xi om}(ro : ga %> de)(sg : de %> xi)(ta : xi %> om)
      -> ((ro %% sg) %% ta) ~ (ro %% (sg %% ta))
  asso [] [] [] = r~
  asso (ro -, x) (sg -, .x) (ta -, .x) rewrite asso ro sg ta = r~
  asso (ro -, x) (sg -, .x) ((ta </ u \> t) -/ .x)
    rewrite opti (ro %% sg) ta
          | opti sg ta
          | opti ro (sg %% ta)
          | asso ro sg ta = r~
  asso (ro -, x) ((sg </ u \> t) -/ .x) ta
    with _ & ta0 , _ & ta1 , v <- coverSub u ta
    rewrite opti ro sg | opti (ro %% sg) ta0
          | opti sg ta0 | opti ro (sg %% ta0)
          | asso ro sg ta0 = r~
  asso ((ro </ u \> t) -/ x) sg ta
    with _ & sg0 , _ & sg1 , v <- coverSub u sg
       | _ & ta0 , _ & ta1 , w <- coverSub v ta
    rewrite opti ro sg0 | opti (ro %% sg0) ta0 | asso ro sg0 ta0
       = {!!}
-}
