module Syntactic.Changes where

-- TERMS that operate on CHANGES
--
-- This module defines terms that correspond to the basic change
-- operations, as well as some other helper terms.

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Syntactic.ChangeTypes.ChangesAreDerivatives

_and_ : ∀ {Γ} → Term Γ bool → Term Γ bool → Term Γ bool
a and b = if a b false

!_ : ∀ {Γ} → Term Γ bool → Term Γ bool
! x = if x false true

-- Term xor
_xor-term_ : ∀ {Γ} → Term Γ bool → Term Γ bool → Term Γ bool
a xor-term b = if a (! b) b

diff-term : ∀ {τ Γ} → Term Γ τ → Term Γ τ → Term Γ (Δ-Type τ)
apply-term : ∀ {τ Γ} → Term Γ (Δ-Type τ) → Term Γ τ → Term Γ τ

apply-term {τ₁ ⇒ τ₂} df f =
  -- λ x . (df x (x ⊝ x)) ⊕ (f x)
  abs (apply-term
        (app (app (weaken¹ df) (var this))
             (diff-term (var this) (var this)))
        (app (weaken¹ f) (var this)))

apply-term {bool} db b =
  db xor-term b

diff-term {τ ⇒ τ₁} f₁ f₂ =
  -- λ x dx. (f₁ (dx ⊕ x)) ⊝ (f₂ x)
  abs (abs (diff-term {τ₁}
             (app (weaken² f₁) (apply-term (var this) (var (that this))))
             (app (weaken² f₂) (var (that this)))))

diff-term {bool} db b =
  db xor-term b
