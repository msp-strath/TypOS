module Examples where

open import Agda.Builtin.String

open import Basics
open import Thin
open import Cop
open import Pair
open import Bind
open import Term
open import Mangler
open import Pub
open import Pat

open THIN {`1}
open COP {`1}
open PAIR {`1}
open BIND {`1}
open PUB {`1}

record AA : Set where
  constructor atom
  field
    code : Nat
open AA

eqNat : (a b : Nat) → Maybe (a ~ b)
eqNat zero zero = aye r~
eqNat (suc a) (suc b) = (| (refl suc ~$~_) (eqNat a b) |)
eqNat x y = naw

eqAA : (a b : AA) → Maybe (a ~ b)
eqAA (atom a) (atom b) = (| (refl atom ~$~_) (eqNat a b) |)

open PAT AA eqAA


pattern App = atom zero
pattern Lam = atom (suc zero)

betaLHS : Pat []
betaLHS = pp (aa App) (pp (pp (aa Lam) (bb (io ??))) (io ??))

open OMATCH (_<P- betaLHS)

open TERM (_<P- betaLHS) AA

betaRHS : Term []
betaRHS = m^ (pr (aa App) (pl (pr (aa Lam) (bb hh)) (io ??)))
             ((os /,\ m^ (pr (aa App) (pr (pp (aa Lam) (bb (([] -, <>) ??))) hh)) os) -/^ _)

beta : forall {ga} -> Term ga -> Maybe (Term ga)
beta {ga} t = do
  pi <- match? ga betaLHS t
  aye (stan'^ betaLHS betaRHS pi)

redex : Term (suc zero)
redex = a^ App ,^ ((a^ Lam ,^ b^ (v^ (no -, _))) ,^ v^ (no -, _))

test = beta redex
