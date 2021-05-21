module CdBsb where

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

data _<=_ {X : Set} : Bwd X -> Bwd X -> Set where
  _-^_ : forall {ga de} -> ga <= de -> forall x -> ga <= (de -, x)
  _-,_ : forall {ga de} -> ga <= de -> forall x -> (ga -, x) <= (de -, x)
  []   : [] <= []
infixl 6 _-,_ _-^_

_&_ : forall {X}{ga de xi : Bwd X} -> ga <= de -> de <= xi -> ga <= xi
th & (ph -^ x) = (th & ph) -^ x
(th -^ .x) & (ph -, x) = (th & ph) -^ x
(th -, .x) & (ph -, x) = (th & ph) -, x
[] & [] = []
infixl 6 _&_

no : forall {X}{ga : Bwd X} -> [] <= ga
no {X} {[]} = []
no {X} {ga -, x} = no -^ x

io : forall {X}{ga : Bwd X} -> ga <= ga
io {X} {[]} = []
io {X} {ga -, x} = io -, x

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
infixr 4 _,_ _*_

[_] <_> : forall {X : Set} -> (X -> Set) -> Set
[ P ] = forall {x} -> P x
< P > = _ >< P
infix 1 <_> [_]

_*:_ _-:>_ : forall {X : Set} -> (X -> Set) -> (X -> Set) -> (X -> Set)
(P *: Q) x = P x * Q x
(P -:> Q) x = P x -> Q x
infixr 7 _*:_
infixr 6 _-:>_

CdB : forall {X} -> (Bwd X -> Set) -> (Bwd X -> Set)
CdB P de = < P *: (_<= de) >

_^_ : forall {X}{P : Bwd X -> Set}{ga de} ->
  CdB P ga -> ga <= de -> CdB P de
(_ , p , th) ^ ph = _ , p , (th & ph)

cop : forall {X}{ga0 de ga1 : Bwd X} ->
  ga0 <= de -> ga1 <= de ->
  < (ga0 <=_) *: (_<= de) *: (ga1 <=_) >
cop (th -^ x) (ph -^ .x) with _ , th' , ps , ph' <- cop th ph
  = _ , th' , ps -^ x , ph'
cop (th -^ x) (ph -, .x) with _ , th' , ps , ph' <- cop th ph
  = _ , th' -^ x , ps -, x , ph' -, x
cop (th -, x) (ph -^ .x) with _ , th' , ps , ph' <- cop th ph
  = _ , th' -, x , ps -, x , ph' -^ x
cop (th -, x) (ph -, .x) with _ , th' , ps , ph' <- cop th ph
  = _ , th' -, x , ps -, x , ph' -, x
cop [] [] = _ , [] , [] , []

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
{-# BUILTIN EQUALITY _~_ #-}

pbk : forall {X}{ga0 de ga1 : Bwd X} ->
  ga0 <= de -> ga1 <= de ->
  < (_<= ga0) *: (_<= de) *: (_<= ga1) >
pbk (th -^ x) (ph -^ .x) with _ , th' , ps , ph' <- pbk th ph
  = _ , th' , ps -^ x , ph'
pbk (th -^ x) (ph -, .x) with _ , th' , ps , ph' <- pbk th ph
  = _ , th' , ps -^ x , ph' -^ x
pbk (th -, x) (ph -^ .x) with _ , th' , ps , ph' <- pbk th ph
  = _ , th' -^ x , ps -^ x , ph'
pbk (th -, x) (ph -, .x) with _ , th' , ps , ph' <- pbk th ph
  = _ , th' -, x , ps -, x , ph' -, x
pbk [] [] = _ , [] , [] , []

not : forall {X}{ga de : Bwd X} -> ga <= de -> < (_<= de) >
not (th -^ x) with _ , ph <- not th = _ , ph -, x
not (th -, x) with _ , ph <- not th = _ , ph -^ x
not [] = _ , []

pbk' : forall {X}{ga0 de ga1 : Bwd X} ->
  (ch : ga0 <= de) -> (th : ga1 <= de) ->
  Bwd X >< \ ga -> 
    (ga <= ga0) >< \ th' ->
    (ga <= de) *
    (ga <= ga1) *
    (fst (not th') <= fst (not th))
pbk' (ch -^ x) (th -^ .x)
  with _ , th' , ps , ch' , nu <- pbk' ch th
     = _ , th' , ps -^ x , ch' , nu -^ x 
pbk' (ch -^ x) (th -, .x)
  with _ , th' , ps , ch' , nu <- pbk' ch th
     = _ , th' , ps -^ x , ch' -^ x , nu
pbk' (ch -, x) (th -^ .x)
  with _ , th' , ps , ch' , nu <- pbk' ch th
     = _ , th' -^ x , ps -^ x , ch' , nu -, x
pbk' (ch -, x) (th -, .x)
  with _ , th' , ps , ch' , nu <- pbk' ch th
     = _ , th' -, x , ps -, x , ch' -, x , nu
pbk' [] [] = [] , [] , [] , [] , []


data All {X : Set}(P : X -> Set) : Bwd X -> Set where
  [] : All P []
  _-,_ : forall {xz x} -> All P xz -> P x -> All P (xz -, x)

_?<_ : forall {X}{P : X -> Set}{ga de : Bwd X} ->
  ga <= de -> All P de -> All P ga
(th -^ x) ?< (pz -, p) = th ?< pz
(th -, x) ?< (pz -, p) = (th ?< pz) -, p
[] ?< [] = []

riffle : forall {X}{P : X -> Set}{ga0 ga1 de : Bwd X} ->
  All P ga0 -> (th : ga0 <= de) -> All P ga1 -> (ph : ga1 <= de) ->
  All P (fst (cop th ph))
riffle pz (th -^ x) qz (ph -^ .x) = riffle pz th qz ph
riffle pz (th -^ x) (qz -, q) (ph -, .x) = riffle pz th qz ph -, q
riffle (pz -, p) (th -, x) qz (ph -^ .x) = riffle pz th qz ph -, p
riffle (pz -, p) (th -, x) (qz -, q) (ph -, .x) = riffle pz th qz ph -, p
riffle [] [] [] [] = []

record One : Set where
  constructor <>

Nat = Bwd One

data Bnd (T : Nat -> Set)(ga : Nat) : Set where
  la : T (ga -, <>) -> Bnd T ga
  ka : T ga -> Bnd T ga

data Tm : Nat -> Set where
  var : Tm ([] -, <>)
  atm : Nat -> Tm []
  _%_ : forall {ga} -> CdB Tm ga -> CdB Tm ga -> Tm ga
  abs : forall {ga} -> Bnd Tm ga -> Tm ga
  
record Sbst (ga de : Nat) : Set where
  constructor sbst
  field
    {acti} : Nat
    hits : acti <= ga
    imgs : All (\ _ -> CdB Tm de) acti
    miss : fst (not hits) <= de

_=>_ : Nat -> Nat -> Set
ga => de = CdB (Sbst ga) de

module _ {X : Set} where

  all : forall {P Q : X -> Set}
     -> [ P -:> Q ]
     -> [ All P -:> All Q ]
  all f [] = []
  all f (pz -, p) = all f pz -, f p

copz : forall {ga de : Nat}
    -> All (\ _ -> CdB Tm de) ga
    -> CdB (\ de -> All (\ _ -> CdB Tm de) ga) de
copz [] = _ , [] , no
copz (tz -, (_ , t , ph))
  with de0 , sz , th <- copz tz
     | _ , th' , ps , ph' <- cop th ph
     = _ , all (_^ th') sz -, (_ , t , ph') , ps

mksb : forall {ga de xi}
    -> (th : xi <= ga)
    -> All (\ _ -> CdB Tm de) xi
    -> fst (not th) <= de
    -> CdB (Sbst ga) de
mksb th iz ph
  with _ , jz , ps0 <- copz iz
     | _ , ps0' , ps , ph' <- cop ps0 ph
     = _ , sbst th (all (_^ ps0') jz) ph' , ps

_?//_ : forall {ga' ga de}(ch : ga' <= ga) -> ga => de -> ga' => de
ch ?// (_ , sbst th iz ph , ps)
  with _ , th' , di , ch' , nu <- pbk' ch th
     | jz <- ch' ?< iz
     = mksb th' jz (nu & ph) ^ ps

blep : forall {X}{ga : Bwd X} -> (th : [] <= ga) ->
       fst (not th) ~ ga
blep (th -^ x) with fst (not th) | blep th
... | de | r~ = r~
blep [] = r~

_%%_ : [ CdB Tm -:> CdB Tm -:> CdB Tm ]
(_ , s , th) %% (_ , t , ph) with _ , th' , ps , ph' <- cop th ph
  = _ , ((_ , s , th') % (_ , t , ph')) , ps

abst : forall {ga} -> CdB Tm (ga -, <>) -> CdB Tm ga
abst (_ , t , th -^ .<>) = _ , abs (ka t) , th
abst (_ , t , th -, .<>) = _ , abs (la t) , th

wksb : forall {ga de} -> ga => de -> (ga -, <>) => (de -, <>)
wksb (_ , sbst th iz ph , ps) =
  _ , sbst (th -^ <>) (all (_^ (io -^ <>)) iz) (ph -, <>) , ps -, <>

_^//_ : forall {ga de} -> CdB Tm ga -> ga => de -> CdB Tm de
_//_ : forall {ga de} -> Tm ga -> ga => de -> CdB Tm de
(_ , t , ch) ^// sg with ch ?// sg
... | _ , sbst th [] ph , ps
  with fst (not th) | blep th
... | _ | r~
  = _ , t , ph & ps
((_ , t , ch) ^// sg) | ta@(_ , sbst th (iz -, x) ph , ps)
  = t // ta
var // (_ , sbst ([] -^ .<>) [] ph , ps) = _ , var , ph & ps  -- never happens
var // (_ , sbst ([] -, .<>) ([] -, t) ph , ps) = t ^ ps
atm a // sg = _ , atm a , no  -- never happens
(s % t) // sg = (s ^// sg) %% (t ^// sg)
abs (la t) // sg = abst (t // wksb sg)
abs (ka t) // sg with _ , u , ph <- t // sg = _ , abs (ka u) , ph

nolem : forall {X}{ga de xi : Bwd X}(th : ga <= de)(ph : xi <= fst (not th))
  -> fst (not ph) ~ fst (not (fst (snd (snd (cop th (ph & snd (not th))))))) 
nolem (th -^ x) (ph -^ .x) rewrite nolem th ph = r~
nolem (th -^ x) (ph -, .x) = nolem th ph
nolem (th -, x) ph = nolem th ph
nolem [] [] = r~

_/&/_ : forall {ga de xi} -> ga => de -> de => xi -> ga => xi
(_ , sbst th0 iz ph0 , ps0) /&/ taph
  with (_ , ta@(sbst th1 jz ph1) , ps1) <- ps0 ?// taph
     | _ , th1' , di , ph0' , th1~ <- pbk' ph0 th1
     | kz <- riffle (all (_^// (_ , ta , io)) iz) th0 (ph0' ?< jz) (th1' & snd (not th0))
     | q <- nolem th0 th1'
     | _ , th0' , th , ch <- cop th0 (th1' & snd (not th0))
     rewrite q
  = _ , sbst th kz (th1~ & ph1) , ps1
