module Solve where

open import Agda.Builtin.String

open import Basics
open import Thin
open import Cop
open import Pair
open import Bind
open import Term

open THIN
open module T (zm : Bwd Nat) = TERM (_<- zm) String
open COP  {`1}
open PAIR {`1}
open BIND {`1}

data Constraint (n : Nat) (zm : Bwd Nat) : Set where
  all : Constraint (suc n) zm -> Constraint n zm
  eq  : ∀ {m p} -> p <= m -> m <- zm -> _%>^_ zm p n -> Term zm n -> Constraint n zm

data Meta (m : Nat)      -- How many global things we can depend on
          (zm : Bwd Nat) -- All the metas in scope
         : Nat           -- How many things we can depend on (morally m + x)
         -> Set where
  lambda : ∀ {p} -> Meta (suc m) zm p -> Meta m zm p
  hole : Meta m zm m
  defn : Term zm m -> Meta m zm m

data Ctx : Nat -- number of object variables in scope
        -> Bwd Nat -- metavariable context
        -> Set where
  [] : Ctx [] []
  _-,_ : ∀ {n zm} -> Ctx n zm -> ∀ x -> Ctx (n -, x) zm
  _-?_ : ∀ {n zm m p} -> Ctx n zm -> m <= n -> Meta m zm p -> Ctx n (zm -, p)

solve : ∀ {n zm m p} -> Ctx n zm -> p <= m -> m <- zm -> _%>^_ zm p n -> Term zm n
     -> Maybe < zm <=_ *: Ctx n >
solve (ctx -, x) et i (sg & ph -^ .x) (tm & th -^ .x) = do
  ps & ctx' <- solve ctx et i (sg & ph) (tm & th)
  aye (ps & ctx' -, x)
solve (ctx -, x) et i (sg & ph -^ .x) (tm & (th -, .x)) = naw
solve {zm = zm} (ctx -, x) et i (sg & (ph -, .x)) (tm & th -^ .x) = do
  let (de & ta) = prune zm (io -^ x) sg
  (ps & ctx') <- solve ctx (de -& et) i (ta |^ ph) (tm & th)
  aye (ps & ctx' -, x)
solve (ctx -, x) et i (sg & (ph -, .x)) (tm & (th -, .x)) = {!!}
solve (_-?_ ctx x m) et i sg tm = {!!}
