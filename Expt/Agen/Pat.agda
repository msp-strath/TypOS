module Pat where

open import Basics
open import Thin
open import Term
open import Pub

open THIN {`1}
open PUB {`1}

module PAT (A : Set) where

  data Pat (ga : Nat) : Set where
    _?? : forall {de} -> de <= ga -> Pat ga
    vv  : ([] -, <>) <= ga -> Pat ga
    aa  : A -> Pat ga
    pp  : Pat ga -> Pat ga -> Pat ga
    bb  : Pat (ga -, <>) -> Pat ga
  infix 50 _??

  infix 30 _?^0_ _?^1_
  
  -- throw in more vars which we don't like
  _?^0_ : forall {ga ga'} -> Pat ga -> ga <= ga' -> Pat ga'
  th ?? ?^0 ph = (th -& ph) ??
  vv x ?^0 ph = vv (x -& ph)
  aa a ?^0 ph = aa a
  pp p q ?^0 ph = pp (p ?^0 ph) (q ?^0 ph)
  bb p ?^0 ph = bb (p ?^0 (ph -, <>))

  -- throw in more vars which we do like
  _?^1_ : forall {ga ga'} -> Pat ga -> ga <= ga' -> Pat ga'
  th ?? ?^1 ph with (_ & th') , _ <- widen (th & ph) = th' ??
  vv x ?^1 ph = vv (x -& ph)
  aa a ?^1 ph = aa a
  pp p q ?^1 ph = pp (p ?^1 ph) (q ?^1 ph)
  bb p ?^1 ph = bb (p ?^1 (ph -, <>))

  infix 30 _<P-_
  data _<P-_ (de : Nat){ga : Nat} : Pat ga -> Set where
    hh : {th : de <= ga} -> de <P- th ??
    pl : forall {p : Pat ga}(x : de <P- p)(q : Pat ga)
      -> de <P- pp p q
    pr : forall (p : Pat ga){q : Pat ga}(x : de <P- q)
      -> de <P- pp p q
    bb : forall {p : Pat (ga -, <>)}(x : de <P- p)
      -> de <P- bb p
