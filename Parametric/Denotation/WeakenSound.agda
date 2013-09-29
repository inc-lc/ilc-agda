import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value
import Parametric.Denotation.Evaluation as Evaluation

module Parametric.Denotation.WeakenSound
  {Base : Type.Structure}
  (Const : Term.Structure Base)
  {⟦_⟧Base : Value.Structure Base}
  (⟦_⟧Const : Evaluation.Structure Const ⟦_⟧Base)
  where
  -- importing modules couldn't resolve constraints
  -- unless Const is explicit.

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const

open import Relation.Binary.PropositionalEquality
open import Base.Denotation.Notation
open import Theorem.CongApp
open import Postulate.Extensionality

weaken-sound : ∀ {Γ₁ Γ₂ τ} {Γ₁≼Γ₂ : Γ₁ ≼ Γ₂}
  (t : Term Γ₁ τ) (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken Γ₁≼Γ₂ t ⟧ ρ ≡ ⟦ t ⟧ (⟦ Γ₁≼Γ₂ ⟧ ρ)

weaken-terms-sound : ∀ {Γ₁ Γ₂ Σ} {Γ₁≼Γ₂ : Γ₁ ≼ Γ₂}
  (terms : Terms Γ₁ Σ) (ρ : ⟦ Γ₂ ⟧) →
  ⟦ weaken-terms Γ₁≼Γ₂ terms ⟧Terms ρ ≡ ⟦ terms ⟧Terms (⟦ Γ₁≼Γ₂ ⟧ ρ)

weaken-terms-sound ∅ ρ = refl
weaken-terms-sound (t • terms) ρ =
  cong₂ _•_ (weaken-sound t ρ) (weaken-terms-sound terms ρ)

weaken-sound {Γ₁≼Γ₂ = Γ₁≼Γ₂} (var x) ρ = weaken-var-sound Γ₁≼Γ₂ x ρ
weaken-sound (app s t) ρ = weaken-sound s ρ ⟨$⟩ weaken-sound t ρ
weaken-sound (abs t) ρ = ext (λ v → weaken-sound t (v • ρ))
weaken-sound {Γ₁} {Γ₂} {Γ₁≼Γ₂ = Γ₁≼Γ₂} (const {Σ} {τ} c args) ρ =
  cong ⟦ c ⟧Const (weaken-terms-sound args ρ)
