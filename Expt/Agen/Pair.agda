module Pair where

open import Basics
open import Thin
open import Cop

module PAIR {X : Set} where
  open THIN {X}
  open COP {X}


  infixr 13 _</\>_ _</_\>_
  record _</\>_ (P Q : Bwd X -> Set) (de : Bwd X) : Set where
    constructor _</_\>_
    field
      {losu rosu} : Bwd X
      {loth} : losu <= de
      {roth} : rosu <= de
      lout : P losu
      pcop : loth /u\ roth
      rout : Q rosu
  open _</\>_

  module _ {P Q : Bwd X -> Set} where
  
    infixr 10 _/,\_
    _/,\_ : [ P ^:_ -:> Q ^:_ -:> P </\> Q ^:_ ]
    p & th /,\ q & ph with (! ! ps & _) , u <- cop th ph = p </ u \> q & ps

    outl : [ P </\> Q ^:_ -:> P ^:_ ]
    outl (p </ u \> q & ps) = p & luth u -& ps

    outr : [ P </\> Q ^:_ -:> Q ^:_ ]
    outr (p </ u \> q & ps) = q & ruth u -& ps

    splay : forall {de}{M : P </\> Q ^: de -> Set} ->
      ((p : P ^: de)(q : Q ^: de) -> M (p /,\ q)) ->
      (x : P </\> Q ^: de) -> M x
    splay {de}{M} m
      (p </ u \> q & ps)
      with z <- m (p & luth u -& ps) (q & ruth u -& ps)
      rewrite copQ u ps
          = z

  data Atom (A : Set) : Bwd X -> Set where
    atom : A -> Atom A []

  `_ : forall {A} -> A -> [ Atom A ^:_ ]
  ` a = atom a & no
  
