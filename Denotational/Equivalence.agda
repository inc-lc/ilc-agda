module Denotational.Equivalence where

-- TERM EQUIVALENCE
--
-- This module defines term equivalence as the relation that
-- identifies terms with the same meaning.

open import Relation.Nullary using (¬_)

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using
  (IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
import Relation.Binary.EqReasoning as EqR

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total

open import Changes
open import ChangeContexts

-- TERMS

-- Term Equivalence

module _ {Γ} {τ} where
  data _≈_ (t₁ t₂ : Term Γ τ) : Set where
    ext-t :
      (∀ ρ → ⟦ t₁ ⟧ ρ ≡ ⟦ t₂ ⟧ ρ) →
      t₁ ≈ t₂

  ≈-refl : Reflexive _≈_
  ≈-refl = ext-t (λ ρ → ≡-refl)

  ≈-sym : Symmetric _≈_
  ≈-sym (ext-t ≈) = ext-t (λ ρ → ≡-sym (≈ ρ))

  ≈-trans : Transitive _≈_
  ≈-trans (ext-t ≈₁) (ext-t ≈₂) = ext-t (λ ρ → ≡-trans (≈₁ ρ) (≈₂ ρ))

  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence = record
    { refl  = ≈-refl
    ; sym   = ≈-sym
    ; trans = ≈-trans
    }

≈-setoid : Context → Type → Setoid _ _
≈-setoid Γ τ = record
  { Carrier       = Term Γ τ
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

≈-app : ∀ {Γ τ₁ τ₂} {t₁ t₂ : Term Γ (τ₁ ⇒ τ₂)} {t₃ t₄ : Term Γ τ₁} →
  t₁ ≈ t₂ → t₃ ≈ t₄ → app t₁ t₃ ≈ app t₂ t₄
≈-app (ext-t ≈₁) (ext-t ≈₂) = ext-t (λ ρ →
  ≡-cong₂ (λ x y → x y) (≈₁ ρ) (≈₂ ρ))

≈-abs : ∀ {Γ τ₁ τ₂} {t₁ t₂ : Term (τ₁ • Γ) τ₂} →
  t₁ ≈ t₂ → abs t₁ ≈ abs t₂
≈-abs (ext-t ≈) = ext-t (λ ρ →
  ext (λ v → ≈ (v • ρ)))

≈-Δ : ∀ {τ Γ} {t₁ t₂ : Term Γ τ} →
  t₁ ≈ t₂ → Δ t₁ ≈ Δ t₂
≈-Δ (ext-t ≈) = ext-t (λ ρ → ≡-diff (≈ (update ρ)) (≈ (ignore ρ)))

module ≈-Reasoning where
  module _ {Γ : Context} {τ : Type} where
    open EqR (≈-setoid Γ τ) public
      hiding (_≡⟨_⟩_)

≈-consistent : ¬ (∀ {Γ τ} (t₁ t₂ : Term Γ τ) → t₁ ≈ t₂)
≈-consistent H with H {∅} true false
... | ext-t x with x ∅
... | ()
