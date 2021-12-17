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

data Ctx : Nat -- number of object variables in scope
        -> Bwd Nat -- metavariable context
        -> Set where
  [] : Ctx [] []
  _-,_ : ∀ {n zm} -> Ctx n zm -> ∀ x -> Ctx (n -, x) zm
  _-?_ : ∀ {n zm m} -> Ctx n zm -> m <= n -> Ctx n (zm -, m)
  _-!_ : ∀ {n zm m} -> Ctx n zm -> Term zm m * m <= n -> Ctx n (zm -, m)

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
solve (ctx -? x) et i sg tm = {!!}
solve (ctx -! x) et i sg tm = {!!}
