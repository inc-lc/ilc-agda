module Thesis.SIRelBigStep.DLangDerive where

open import Thesis.SIRelBigStep.DSyntax public

derive-dvar : ∀ {Δ σ} → (x : Var Δ σ) → Var (ΔΔ Δ) (Δτ σ)
derive-dvar this = this
derive-dvar (that x) = that (derive-dvar x)

derive-dterm : ∀ {Δ σ} → (t : Term Δ σ) → DTerm Δ σ

derive-dsval : ∀ {Δ σ} → (t : SVal Δ σ) → DSVal Δ σ
derive-dsval (var x) = dvar (derive-dvar x)

derive-dsval (abs t) = dabs (derive-dterm t)

derive-dterm (val x) = dval (derive-dsval x)
derive-dterm (const c) = dconst c
derive-dterm (app vs vt) = dapp (derive-dsval vs) vt (derive-dsval vt)
derive-dterm (lett s t) = dlett s (derive-dterm s) (derive-dterm t)

-- Nontrivial because of unification problems in pattern matching. I wanted to
-- use it to define ⊕ on closures purely on terms of the closure change.

-- Instead, I decided to use decidable equality on contexts: that's a lot of
-- tedious boilerplate, but not too hard, but the proof that validity and ⊕
-- agree becomes easier.
-- -- Define a DVar and be done?
-- underive-dvar :  ∀ {Δ σ} → Var (ΔΔ Δ) (Δτ σ) → Var Δ σ
-- underive-dvar {∅} ()
-- underive-dvar {τ • Δ} x = {!!}

--underive-dvar {σ • Δ} (that x) = that (underive-dvar x)
