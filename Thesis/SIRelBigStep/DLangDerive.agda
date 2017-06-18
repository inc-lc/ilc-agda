module Thesis.SIRelBigStep.DLangDerive where

open import Thesis.SIRelBigStep.DSyntax public

derive-const : ∀ {Δ σ} → (c : Const σ) → DSVal Δ σ
derive-const (lit n) = dconst (lit 0)

derive-dterm : ∀ {Δ σ} → (t : Term Δ σ) → DTerm Δ σ

derive-dsval : ∀ {Δ σ} → (t : SVal Δ σ) → DSVal Δ σ
derive-dsval (var x) = dvar x
derive-dsval (abs t) = dabs (derive-dterm t)
derive-dsval (cons sv1 sv2) = dcons (derive-dsval sv1) (derive-dsval sv2)
derive-dsval (const c) = derive-const c

derive-dterm (val x) = dval (derive-dsval x)
derive-dterm (primapp p sv) = dprimapp p sv (derive-dsval sv)
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
