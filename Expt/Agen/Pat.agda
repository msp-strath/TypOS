module Pat where

open import Basics
open import Thin
open import Cop
open import Pair
open import Bind
open import Term
open import Pub

open THIN {`1}
open COP {`1}
open PAIR {`1}
open BIND {`1}
open PUB {`1}

module PAT
  (A : Set)
  (eq? : (a b : A) -> Maybe (a ~ b))
  where

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

  module OMATCH (M : Nat -> Set) where

    open TERM M A

    Env : forall (xi : Nat){ga} -> Pat ga -> Set
    Env xi (_?? {de} th) = Term (xi <<< de)
    Env xi (vv x) = `1
    Env xi (aa x) = `1
    Env xi (pp l r) = Env xi l * Env xi r
    Env xi (bb p) = Env xi p

    match? : forall xi {ga}
      (p : Pat ga)(t : Term (xi <<< ga))
      -> Maybe (Env xi p)
    match? xi {ga} (ph ??) (t & th) with thChop ga th
    match? xi {ga} (ph ??) (t & .(th0 +^+ th1)) | ! th0 , th1 , r~ , r~
      = thicken? ph th1 >M= \ (ps , _) ->
      aye (t & th0 +^+ ps)
    match? xi (vv x) (vv only & th) with pub (no {xi} +^+ x) th
    match? xi (vv x) (vv only & th) | [] -^ .<> & v , w = naw
    match? xi (vv x) (vv only & th) | [] -, .<> & v , w = aye <>
    match? xi (aa a) (aa (atom b) & _)  = eq? a b >M= \ _ -> aye <>
    match? xi (pp lp rp) (pp t & th) =
      match? xi lp (outl (t & th)) >M= \ lpi ->
      match? xi rp (outr (t & th)) >M= \ rpi ->
      aye (lpi , rpi) 
    match? xi (bb p) (bb b & th) = match? xi p (under (b & th))
    match? _ _ _ = naw

  module MATCH (M : Nat -> Set) where

    open TERM M A

    Env : forall {ga} -> Pat ga -> Set
    Env (_?? {de} th) = Term de
    Env (vv x) = `1
    Env (aa x) = `1
    Env (pp l r) = Env l * Env r
    Env (bb p) = Env p

    proj : forall {ga}{p : Pat ga} -> Env p ->
           [ _<P- p -:> Term ]
    proj t hh = t
    proj (pi , _) (pl i q) = proj pi i
    proj (_ , pi) (pr p i) = proj pi i
    proj pi (bb i) = proj pi i

    -- try to throw some vars out of scope
    _<?_ : forall {ga ga'} -> ga <= ga' -> (p' : Pat ga')
        -> Maybe (Pat ga >< \ p -> Env p -> Env p')
    ph <? (th ??) with ph' & th' , _ <- pub ph th = aye (ph' ?? , \ t -> mu^ (t & th') )
    ph <? vv x = (| (_, _) (| vv (| fst (thicken? ph x) |) |) |) -- (| vv (| fst (thicken? ph x) |) |)
    ph <? aa a = (| (_, _) (| (aa a) |) |) -- (| (aa a) |)
    ph <? pp p q = (ph <? p) >M= \ (p , f) -> (ph <? q) >M= \ (q , g) ->
      aye (pp p q , (f >><< g)) 
    ph <? bb p = (| (bb >><< id) ((ph -, <>) <? p) |)

    match? : forall {ga}(p : Pat ga)(t : Term ga)
      -> Maybe (Env p)
    match? (ph ??) (t & th) = 
      thicken? ph th >M= \ (ps , _) ->
      aye (t & ps)
    match? (vv x) (vv only & th) with pub x th
    ... | ([] , _) , _ = naw
    ... | (_ -, _ , _) , _ = aye <>
    match? (aa a) (aa (atom b) & th) =
      eq? a b >M= \ _ -> aye <>
    match? (pp lp rp) (pp t & th) = 
      match? lp (outl (t & th)) >M= \ lpi ->
      match? rp (outr (t & th)) >M= \ rpi ->
      aye (lpi , rpi) 
    match? (bb p) (bb b & th) = match? p (under (b & th))
    match? _ _ = ff , <>

    mitch? : forall {ga}(p : Pat ga)(t : Tm ga) -> Maybe (Env p)
    mitch? (th ??) t = all? th >M= \ { (r~ , _) -> aye (t & io) }
    mitch? (vv x) (vv only) = aye <>
    mitch? (aa a) (aa (atom b)) = (| (ko <>) (eq? a b) |)
    mitch? (pp p q) (pp (s </ u \> t)) =
      (luth u <? p) >M= \ (p , f) ->
      (ruth u <? q) >M= \ (q , g) ->
      (| (| f (mitch? p s) |) , (| g (mitch? q t) |) |)
    mitch? (bb p) (bb (kk t)) =
      ((io -^ <>) <? p) >M= \ (p , f) ->
      (| f (mitch? p t) |)
    mitch? (bb p) (bb (ll t)) = mitch? p t
    mitch? _ _ = naw

    data _<P=_ {ga : Nat} : Pat ga -> Pat ga -> Set where
      mm : forall {de p'} p {th : de <= ga}
         -> p' ~ p ?^0 th    -- define this relationally?
         -> p' <P= (th ??)
      vv  : (x : ([] -, <>) <= ga) -> vv x <P= vv x
      aa  : (a : A) -> aa a <P= aa a
      pp  : {l l' r r' : Pat ga} -> l <P= l' -> r <P= r'
         -> pp l r <P= pp l' r'
      bb  : {p p' : Pat (ga -, <>)} -> p <P= p'
         -> bb p <P= bb p'

    data Botify {X : Set}(R : X -> X -> Set) : Maybe X -> Maybe X -> Set where
      bot  : forall {y} -> Botify R naw y
      lift : forall {x y} -> R x y -> Botify R (aye x) (aye y)

    _<?=_ : {ga : Nat} -> Maybe (Pat ga) -> Maybe (Pat ga) -> Set
    _<?=_ = Botify _<P=_

    exclude : forall {ga de}(th : ga <= de)(p : Pat de) ->
      Maybe (Pat ga >< \ p0 -> Pat de >< \ p1 ->
        p1 ~ p0 ?^0 th * p1 <P= p)
    exclude th (ph ??)
      with th' & ph' , (ps , v , w) , b <- pub th ph
         = aye (th' ?? , ps ??
               , (refl _?? ~$~ fst (triQ (! v) (tri th' th)))
               , mm (ph' ??) (refl _?? ~$~ fst (triQ (! w) (tri ph' ph))))
    exclude th (vv x) = thicken? th x >M= \ (y , v) ->
      aye (vv y , vv x , (refl vv ~$~ fst (triQ (! v) (tri y th))) , vv x)
    exclude th (aa a) = aye (aa a , aa a , r~ , aa a)
    exclude th (pp p q)
      with exclude th p | exclude th q
    ... | aye (p0 , p1 , p~ , p<) | aye (q0 , q1 , q~ , q<)
        = aye (pp p0 q0 , pp p1 q1 , (refl pp ~$~ p~ ~$~ q~) , pp p< q<)
    ... | _ | _ = naw
    exclude th (bb p) =
      exclude (th -, _) p >M= \ (p0 , p1 , p~ , p<) ->
      aye (bb p0 , bb p1 , (refl bb ~$~ p~) , bb p<)

    unify : {ga : Nat}(p q : Pat ga) -> < _<?= aye p *: _<?= aye q >
    unify (th ??) p with exclude th p
    ... | aye (p0 , p1 , p~ , p<) = lift (mm p0 p~) & lift p<
    ... | _ = bot & bot
    unify p (th ??) with exclude th p
    ... | aye (p0 , p1 , p~ , p<) = lift p< & lift (mm p0 p~)
    ... | _ = bot & bot
    unify (vv x) (vv y) with pub x y
    ... | ([] , _) , _ = bot & bot
    unify (vv x) (vv y) | (_ -, _ , ([] -, <>) , ([] -, <>)) , b & c , _
      with r~ , r~ <- lio b , lio c = lift (vv y) & lift (vv x)
    unify (aa a) (aa b) with eq? a b
    ... | aye r~ = lift (aa b) & lift (aa a)
    ... | naw    = bot & bot
    unify (pp lp rp) (pp lq rq) with unify lp lq | unify rp rq
    ... | lift ulp & lift ulq | lift urp & lift urq
        = lift (pp ulp urp) & lift (pp ulq urq)
    ... | _ | _ = bot & bot
    unify (bb p) (bb q) with unify p q
    ... | lift up & lift uq = lift (bb up) & lift (bb uq)
    ... | _ = bot & bot
    unify _ _ = bot & bot
