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

apply-pure-term {τ₁ ⇒ τ₂} {Γ} =
-- λdf. λf.  λx.            apply          (          df                       x          (x ⊖ x))                             (     f                x        )
   abs (abs (abs (app (app apply-pure-term (app (app (var (that (that this))) (var this)) (diff-term (var this) (var this)))) (app (var (that this)) (var this)))))
--abs (abs (abs (app (app apply-compose-term (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))


apply-term : ∀ {τ Γ} → Term Γ (Δ-Type τ) → Term Γ τ → Term Γ τ
apply-term {τ ⇒ τ₁} = λ df f → app (app apply-pure-term df) f
apply-term {bool} = _xor-term_

diff-term {τ ⇒ τ₁} =
  λ f₁ f₂ →
  -- The following can be written as:
  -- * Using Unicode symbols for change operations:
  -- λ x dx. (f1 (dx ⊕ x)) ⊝ (f2 x)
  -- * In lambda calculus with names:
  --λx.  λdx. diff           (     f₁                   (apply      dx         x))                 (f₂                        x)
  -- * As a deBrujin-encoded term in Agda:
    abs (abs (diff-term {τ₁} (app (weaken ≼-in-body f₁) (apply-term (var this) (var (that this)))) (app (weaken ≼-in-body f₂) (var (that this)))))
  where
    ≼-in-body = drop (Δ-Type τ) • (drop τ • ≼-refl)

diff-term {bool} = _xor-term_
