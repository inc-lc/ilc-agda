module Denotational.Evaluation.Total where

-- EVALUATION with a primitive for TOTAL DERIVATIVES
--
-- This module defines the semantics of terms that support a
-- primitive (Δ e) for computing the total derivative according
-- to all free variables in e and all future arguments of e if e
-- is a function.

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type

open import Changes
open import ChangeContexts

-- TERMS

-- Denotational Semantics

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ app t₁ t₂ ⟧Term ρ = (⟦ t₁ ⟧Term ρ) (⟦ t₂ ⟧Term ρ)
⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
⟦ true ⟧Term ρ = true
⟦ false ⟧Term ρ = false
⟦ if t₁ t₂ t₃ ⟧Term ρ with ⟦ t₁ ⟧Term ρ
... | true = ⟦ t₂ ⟧Term ρ
... | false = ⟦ t₃ ⟧Term ρ
⟦ Δ {{Γ′}} t ⟧Term ρ = diff (⟦ t ⟧Term (update (⟦ Γ′ ⟧ ρ))) (⟦ t ⟧Term (ignore (⟦ Γ′ ⟧ ρ)))

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

-- PROPERTIES of WEAKENING

weaken-sound : ∀ {Γ₁ Γ₂ τ} (t : Term Γ₁ τ) {Γ′ : Γ₁ ≼ Γ₂} →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken Γ′ t ⟧ ρ ≡ ⟦ t ⟧ (⟦ Γ′ ⟧ ρ)
weaken-sound (abs t) ρ = ext (λ v → weaken-sound t (v • ρ))
weaken-sound (app t₁ t₂) ρ = ≡-app (weaken-sound t₁ ρ) (weaken-sound t₂ ρ)
weaken-sound (var x) ρ = lift-sound _ x ρ
weaken-sound true ρ = refl
weaken-sound false ρ = refl
weaken-sound (if t₁ t₂ t₃) {Γ′} ρ with weaken-sound t₁ {Γ′} ρ
... | H with ⟦ weaken Γ′ t₁ ⟧ ρ | ⟦ t₁ ⟧ (⟦ Γ′ ⟧ ρ)
weaken-sound (if t₁ t₂ t₃) {Γ′} ρ | refl | true | true = weaken-sound t₂ {Γ′} ρ
weaken-sound (if t₁ t₂ t₃) {Γ′} ρ | refl | false | false = weaken-sound t₃ {Γ′} ρ
weaken-sound (Δ {{Γ′}} t) {Γ″} ρ =
  cong (λ x → diff (⟦ t ⟧ (update x)) (⟦ t ⟧ (ignore x))) (⟦⟧-≼-trans Γ′ Γ″ ρ)
