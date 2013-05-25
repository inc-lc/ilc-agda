module Denotational.Equivalence where

-- TERM EQUIVALENCE
--
-- This module defines term equivalence as the relation that
-- identifies terms with the same meaning.

open import Relation.Nullary using (¬_)

open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

open import Denotational.Notation

-- TERMS

-- Term Equivalence
--
-- This module is parametric in the syntax and semantics of types
-- and terms to make it work for different calculi.

module _ where
  open import Syntactic.Contexts
  open import Denotational.Environments

  module MakeEquivalence
      (Type : Set)
      (⟦_⟧Type : Type → Set)
      (Term : Context Type → Type → Set)
      (⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦_⟧Context Type ⟦_⟧Type Γ → ⟦ τ ⟧Type) where
    module _ {Γ} {τ} where
      data _≈_ (t₁ t₂ : Term Γ τ) : Set where
        ext-t :
          (∀ ρ → ⟦ t₁ ⟧Term ρ ≡ ⟦ t₂ ⟧Term ρ) →
          t₁ ≈ t₂

      ≈-refl : Reflexive _≈_
      ≈-refl = ext-t (λ ρ → refl)

      ≈-sym : Symmetric _≈_
      ≈-sym (ext-t ≈) = ext-t (λ ρ → sym (≈ ρ))

      ≈-trans : Transitive _≈_
      ≈-trans (ext-t ≈₁) (ext-t ≈₂) = ext-t (λ ρ → trans (≈₁ ρ) (≈₂ ρ))

      ≈-isEquivalence : IsEquivalence _≈_
      ≈-isEquivalence = record
        { refl  = ≈-refl
        ; sym   = ≈-sym
        ; trans = ≈-trans
        }

    ≈-setoid : Context Type → Type → Setoid _ _
    ≈-setoid Γ τ = record
      { Carrier       = Term Γ τ
      ; _≈_           = _≈_
      ; isEquivalence = ≈-isEquivalence
      }

    module ≈-Reasoning where
      module _ {Γ : Context Type} {τ : Type} where
        open import Relation.Binary.EqReasoning (≈-setoid Γ τ) public
          hiding (_≡⟨_⟩_)

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total
open import Syntactic.Changes

open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total

open import Changes
open import ChangeContexts

-- Export a version of the equivalence for terms with total
-- derivatives

open MakeEquivalence Type ⟦_⟧ Term ⟦_⟧ public

-- Specialized congruence rules

≈-app : ∀ {Γ τ₁ τ₂} {t₁ t₂ : Term Γ (τ₁ ⇒ τ₂)} {t₃ t₄ : Term Γ τ₁} →
  t₁ ≈ t₂ → t₃ ≈ t₄ → app t₁ t₃ ≈ app t₂ t₄
≈-app (ext-t ≈₁) (ext-t ≈₂) = ext-t (λ ρ →
  ≡-cong₂ (λ x y → x y) (≈₁ ρ) (≈₂ ρ))

≈-abs : ∀ {Γ τ₁ τ₂} {t₁ t₂ : Term (τ₁ • Γ) τ₂} →
  t₁ ≈ t₂ → abs t₁ ≈ abs t₂
≈-abs (ext-t ≈) = ext-t (λ ρ →
  ext (λ v → ≈ (v • ρ)))

≈-Δ : ∀ {τ Γ₁ Γ₂} (Γ′ : Δ-Context Γ₁ ≼ Γ₂) {t₁ t₂ : Term Γ₁ τ} →
  t₁ ≈ t₂ → Δ Γ′ t₁ ≈ Δ Γ′ t₂
≈-Δ Γ′ (ext-t ≈) = ext-t (λ ρ → ≡-diff (≈ (update (⟦ Γ′ ⟧ ρ))) (≈ (ignore (⟦ Γ′ ⟧ ρ))))

≈-true : ∀ {Γ} → _≈_ {Γ} true true
≈-true = ≈-refl

≈-false : ∀ {Γ} → _≈_ {Γ} false false
≈-false = ≈-refl

≈-if : ∀ {τ Γ} {t₁ t₂ : Term Γ bool} {t₃ t₄ t₅ t₆ : Term Γ τ} →
  t₁ ≈ t₂ → t₃ ≈ t₄ → t₅ ≈ t₆ → if t₁ t₃ t₅ ≈ if t₂ t₄ t₆
≈-if (ext-t ≈₁) (ext-t ≈₂) (ext-t ≈₃) = ext-t (λ ρ → ≡-if ≈₁ ρ then ≈₂ ρ else ≈₃ ρ)

≈-weaken : ∀ {τ Γ₁ Γ₂} (Γ′ : Γ₁ ≼ Γ₂) {t₁ t₂ : Term Γ₁ τ} →
  t₁ ≈ t₂ → weaken Γ′ t₁ ≈ weaken Γ′ t₂
≈-weaken Γ′ {t₁} {t₂} (ext-t ≈₁) = ext-t (λ ρ →
  begin
    ⟦ weaken Γ′ t₁ ⟧ ρ
  ≡⟨ weaken-sound t₁ ρ ⟩
    ⟦ t₁ ⟧Term (⟦ Γ′ ⟧≼ ρ)
  ≡⟨ ≈₁ (⟦ Γ′ ⟧≼ ρ) ⟩
    ⟦ t₂ ⟧Term (⟦ Γ′ ⟧≼ ρ)
  ≡⟨ ≡-sym (weaken-sound t₂ ρ) ⟩
    ⟦ weaken Γ′ t₂ ⟧ ρ
  ∎) where open ≡-Reasoning

-- Computation Rules

≈-if-true : ∀ {τ Γ} {t₁ : Term Γ bool} {t₂ t₃ : Term Γ τ} →
  t₁ ≈ true → if t₁ t₂ t₃ ≈ t₂
≈-if-true {_} {_} {t₁} {t₂} {t₃} (ext-t ≈₁) = ext-t (λ ρ →
  begin
    ⟦ if t₁ t₂ t₃ ⟧ ρ
  ≡⟨⟩
    ( if ⟦ t₁ ⟧ ρ then ⟦ t₂ ⟧ ρ else ⟦ t₃ ⟧ ρ )
  ≡⟨ ≡-if ≈₁ ρ then ≡-refl else ≡-refl ⟩
    ( if true then ⟦ t₂ ⟧ ρ else ⟦ t₃ ⟧ ρ )
  ≡⟨⟩
    ⟦ t₂ ⟧ ρ
  ∎) where open ≡-Reasoning

≈-if-false : ∀ {τ Γ} {t₁ : Term Γ bool} {t₂ t₃ : Term Γ τ} →
  t₁ ≈ false → if t₁ t₂ t₃ ≈ t₃
≈-if-false {_} {_} {t₁} {t₂} {t₃} (ext-t ≈₁) = ext-t (λ ρ →
  begin
    ⟦ if t₁ t₂ t₃ ⟧ ρ
  ≡⟨⟩
    ( if ⟦ t₁ ⟧ ρ then ⟦ t₂ ⟧ ρ else ⟦ t₃ ⟧ ρ )
  ≡⟨ ≡-if ≈₁ ρ then ≡-refl else ≡-refl ⟩
    ( if false then ⟦ t₂ ⟧ ρ else ⟦ t₃ ⟧ ρ )
  ≡⟨⟩
    ⟦ t₃ ⟧ ρ
  ∎) where open ≡-Reasoning

-- Consistency

≈-consistent : ¬ (∀ {Γ τ} (t₁ t₂ : Term Γ τ) → t₁ ≈ t₂)
≈-consistent H with H {∅} true false
... | ext-t x with x ∅
... | ()

-- Derived congruence rules for named terms

_≈-and_ : ∀ {Γ} {t₁ t₂ t₃ t₄ : Term Γ bool} →
  t₁ ≈ t₂ → t₃ ≈ t₄ → (t₁ and t₃) ≈ (t₂ and t₄)
_≈-and_ ≈₁ ≈₂ = ≈-if ≈₁ ≈₂ ≈-false

≈-!_ : ∀ {Γ} {t₁ t₂ : Term Γ bool} →
  t₁ ≈ t₂ → ! t₁ ≈ ! t₂
≈-!_ ≈₁ = ≈-if ≈₁ ≈-false ≈-true

_≈-xor-term_ : ∀ {Γ} {t₁ t₂ t₃ t₄ : Term Γ bool} →
  t₁ ≈ t₂ → t₃ ≈ t₄ → (t₁ xor-term t₃) ≈ (t₂ xor-term t₄)
_≈-xor-term_ ≈₁ ≈₂ = ≈-if ≈₁ (≈-! ≈₂) ≈₂

≈-diff-term : ∀ {τ Γ} {t₁ t₂ t₃ t₄ : Term Γ τ} →
  t₁ ≈ t₂ → t₃ ≈ t₄ → diff-term t₁ t₃ ≈ diff-term t₂ t₄
≈-diff-term {τ₁ ⇒ τ₂} ≈₁ ≈₂ =
  ≈-abs (≈-abs
    (≈-diff-term
      (≈-app (≈-weaken Γ″ ≈₁) ≈-refl)
      (≈-app (≈-weaken Γ″ ≈₂) ≈-refl)))
  where
    Γ″ = drop (Δ-Type τ₁) • (drop τ₁ • ≼-refl)
≈-diff-term {bool} ≈₁ ≈₂ = ≈₁ ≈-xor-term ≈₂

≈-apply-term : ∀ {τ Γ} {t₁ t₂ : Term Γ (Δ-Type τ)} {t₃ t₄ : Term Γ τ} →
  t₁ ≈ t₂ → t₃ ≈ t₄ → apply-term t₁ t₃ ≈ apply-term t₂ t₄
≈-apply-term {τ₁ ⇒ τ₂} ≈₁ ≈₂ =
  ≈-abs (≈-apply-term
          (≈-app (≈-app (≈-weaken Γ″ ≈₁) ≈-refl) ≈-refl)
          (≈-app (≈-weaken Γ″ ≈₂) ≈-refl))
  where
    Γ″ = drop τ₁ • ≼-refl
≈-apply-term {bool} ≈₁ ≈₂ = ≈₁ ≈-xor-term ≈₂
