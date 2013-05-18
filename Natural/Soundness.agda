module Natural.Soundness where

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total
open import Syntactic.Closures

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total
open import Denotational.Equivalence
open import Denotational.Closures

open import Natural.Lookup
open import Natural.Evaluation

-- SOUNDNESS of natural semantics

↦-sound : ∀ {Γ τ ρ v} {x : Var Γ τ} →
  ρ ⊢ x ↦ v →
  ⟦ x ⟧ ⟦ ρ ⟧ ≡ ⟦ v ⟧
↦-sound this = ≡-refl
↦-sound (that ↦) = ↦-sound ↦

↓-sound : ∀ {Γ τ ρ v} {t : Term Γ τ} →
  ρ ⊢ t ↓ v →
  ⟦ t ⟧ ⟦ ρ ⟧ ≡ ⟦ v ⟧
↓-sound abs = ≡-refl
↓-sound (app ↓₁ ↓₂ ↓′) =
  ≡-trans
    (≡-cong₂ (λ x y → x y) (↓-sound ↓₁) (↓-sound ↓₂))
    (↓-sound ↓′)
↓-sound (var ↦) = ↦-sound ↦
