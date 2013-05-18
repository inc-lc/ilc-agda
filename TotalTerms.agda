module TotalTerms where

-- TERMS with a primitive for TOTAL DERIVATIVES
--
-- This module defines the syntax of terms that support a
-- primitive (Δ e) for computing the total derivative according
-- to all free variables in e and all future arguments of e if e
-- is a function.

-- EVALUATION with a primitive for TOTAL DERIVATIVES
--
-- This module defines the semantics of terms that support a
-- primitive (Δ e) for computing the total derivative according
-- to all free variables in e and all future arguments of e if e
-- is a function.

-- TERM EQUIVALENCE
--
-- This module defines term equivalence as the relation that
-- identifies terms with the same meaning.

open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary using
  (IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
import Relation.Binary.EqReasoning as EqR

open import Relation.Nullary using (¬_)

open import Syntactic.Types
open import Denotational.Notation
open import Denotational.Values
open import Changes
open import ChangeContexts
open import binding Type ⟦_⟧Type

-- TERMS

-- Syntax

data Term : Context → Type → Set where
  abs : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {Γ τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ

  true false : ∀ {Γ} → Term Γ bool
  if : ∀ {Γ τ} → (t₁ : Term Γ bool) (t₂ t₃ : Term Γ τ) → Term Γ τ

  -- `Δ t` describes how t changes if its free variables or arguments change
  Δ : ∀ {Γ τ} → (t : Term Γ τ) → Term (Δ-Context Γ) (Δ-Type τ)
  weakenOne : ∀ Γ₁ τ₂ {Γ₃ τ} → Term (Γ₁ ⋎ Γ₃) τ → Term (Γ₁ ⋎ (τ₂ • Γ₃)) τ

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
⟦ Δ t ⟧Term ρ = diff (⟦ t ⟧Term (update ρ)) (⟦ t ⟧Term (ignore ρ))
⟦ weakenOne Γ₁ τ₂ t ⟧Term ρ = ⟦ t ⟧Term (weakenEnv Γ₁ τ₂ ρ)

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

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

substTerm : ∀ {τ Γ₁ Γ₂} → Γ₁ P.≡ Γ₂ → Term Γ₁ τ → Term Γ₂ τ
substTerm {τ} {Γ₁} {Γ₂} ≡₁ t = subst (λ Γ → Term Γ τ) ≡₁ t
