module Thesis.SIRelBigStep.SemEquiv where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Thesis.SIRelBigStep.Syntax public
open import Thesis.SIRelBigStep.OpSem
open import Thesis.SIRelBigStep.DenSem

⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧Type
⟦_⟧Env : ∀ {Γ} → ⟦ Γ ⟧Context → Den.⟦ Γ ⟧Context

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ closure t ρ ⟧Val = λ v → (⟦ t ⟧Term) (v • ⟦ ρ ⟧Env)
⟦ natV n ⟧Val = n

↦-sound : ∀ {Γ τ} ρ (x : Var Γ τ) →
  Den.⟦ x ⟧Var ⟦ ρ ⟧Env ≡ ⟦ ⟦ x ⟧Var ρ ⟧Val
↦-sound (px • ρ) this = refl
↦-sound (px • ρ) (that x) = ↦-sound ρ x

-- Check it's fine to use i 1 in the above proofs.
↓-sv-1-step : ∀ {Γ τ ρ v} {n} {sv : SVal Γ τ} →
  ρ ⊢ val sv ↓[ i' n ] v →
  n ≡ 1
↓-sv-1-step abs = refl
↓-sv-1-step (var x) = refl

↓-sound : ∀ {Γ τ ρ v hasIdx} {n : Idx hasIdx} {t : Term Γ τ} →
  ρ ⊢ t ↓[ n ] v →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val
↓-sound abs = refl
↓-sound (app _ _ ↓₁ ↓₂ ↓′) rewrite ↓-sound ↓₁ | ↓-sound ↓₂ | ↓-sound ↓′ = refl
↓-sound (var x) = ↦-sound _ x
↓-sound (lit n) = refl
↓-sound (lett n1 n2 vsv s t ↓ ↓₁) rewrite ↓-sound ↓ | ↓-sound ↓₁ = refl
-- ↓-sound (add ↓₁ ↓₂) rewrite ↓-sound ↓₁ | ↓-sound ↓₂ = refl
-- ↓-sound (minus ↓₁ ↓₂) rewrite ↓-sound ↓₁ | ↓-sound ↓₂ = refl

-- No proof of completeness yet: the statement does not hold here.
