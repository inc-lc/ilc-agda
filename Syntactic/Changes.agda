module Syntactic.Changes where

-- TERMS that operate on CHANGES
--
-- This module defines terms that correspond to the basic change
-- operations, as well as some other helper terms.

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Changes

_and_ : ∀ {Γ} → Term Γ bool → Term Γ bool → Term Γ bool
a and b = if a b false

!_ : ∀ {Γ} → Term Γ bool → Term Γ bool
! x = if x false true

-- Term xor
_xor-term_ : ∀ {Γ} → Term Γ bool → Term Γ bool → Term Γ bool
a xor-term b = if a (! b) b

diff-term : ∀ {τ Γ} → Term Γ τ → Term Γ τ → Term Γ (Δ-Type τ)

-- XXX: to finish this, we just need to call lift-term, like in
-- derive-term. Should be easy, just a bit boring.
-- Other problem: in fact, Δ t is not the nil change of t, in this context. That's a problem.
apply-pure-term : ∀ {τ Γ} → Term Γ (Δ-Type τ ⇒ τ ⇒ τ)
apply-pure-term {bool} = abs (abs (var this xor-term var (that this)))
apply-pure-term {τ₁ ⇒ τ₂} {Γ} = abs (abs (abs (app (app apply-pure-term (app (app (var (that (that this))) (var this)) (diff-term (var this) (var this)))) (app (var (that this)) (var this)))))
--abs (abs (abs (app (app apply-compose-term (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))
-- λdf. λf.  λx.           apply (     df                       x       (Δx))  (     f                 x        )

apply-term : ∀ {τ Γ} → Term Γ (Δ-Type τ) → Term Γ τ → Term Γ τ
apply-term {τ ⇒ τ₁} = λ df f → app (app apply-pure-term df) f
apply-term {bool} = _xor-term_

diff-term {τ ⇒ τ₁} =
  λ f₁ f₂ →
  -- The following can be written as:
  -- * Using Unicode symbols for change operations:
  -- λ x dx. (f1 (dx ⊝ x)) ⊝ (f2 x)
  -- * In lambda calculus with names:
  --λx.  λdx. diff           (     f₁                   (apply      dx         x))                 (f₂                        x)
  -- * As a deBrujin-encoded term in Agda:
    abs (abs (diff-term {τ₁} (app (weaken ≼-in-body f₁) (apply-term (var this) (var (that this)))) (app (weaken ≼-in-body f₂) (var (that this)))))
  where
    ≼-in-body = drop (Δ-Type τ) • (drop τ • ≼-refl)

diff-term {bool} = _xor-term_

-- Derived CONGRUENCE RULES
module _ where
  open import Denotational.Equivalence

  _≈-and_ : ∀ {Γ} {t₁ t₂ t₃ t₄ : Term Γ bool} →
    t₁ ≈ t₂ → t₃ ≈ t₄ → (t₁ and t₃) ≈ (t₂ and t₄)
  _≈-and_ ≈₁ ≈₂ = ≈-if ≈₁ ≈₂ ≈-false

  ≈-!_ : ∀ {Γ} {t₁ t₂ : Term Γ bool} →
    t₁ ≈ t₂ → ! t₁ ≈ ! t₂
  ≈-!_ ≈₁ = ≈-if ≈₁ ≈-false ≈-true

  _≈-xor-term_ : ∀ {Γ} {t₁ t₂ t₃ t₄ : Term Γ bool} →
    t₁ ≈ t₂ → t₃ ≈ t₄ → (t₁ xor-term t₃) ≈ (t₂ xor-term t₄)
  _≈-xor-term_ ≈₁ ≈₂ = ≈-if ≈₁ (≈-! ≈₂) ≈₂
