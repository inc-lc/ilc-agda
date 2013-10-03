import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value

module Parametric.Denotation.Evaluation
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base

open import Base.Denotation.Notation

open import Relation.Binary.PropositionalEquality
open import Theorem.CongApp
open import Postulate.Extensionality

Structure : Set
Structure = ∀ {Σ τ} → Const Σ τ → ⟦ Σ ⟧ → ⟦ τ ⟧

module Structure (⟦_⟧Const : Structure) where
  ⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧

  ⟦_⟧Terms : ∀ {Γ Σ} → Terms Γ Σ → ⟦ Γ ⟧ → ⟦ Σ ⟧

  ⟦ const c args ⟧Term ρ = ⟦ c ⟧Const (⟦ args ⟧Terms ρ)
  ⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
  ⟦ app s t ⟧Term ρ = (⟦ s ⟧Term ρ) (⟦ t ⟧Term ρ)
  ⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)

  -- this is what we'd like to write.
  -- unfortunately termination checker complains.
  --
  --   ⟦ terms ⟧Terms ρ = map-IVT (λ t → ⟦ t ⟧Term ρ) terms
  --
  -- so we do explicit pattern matching instead.
  ⟦ ∅ ⟧Terms ρ = ∅
  ⟦ s • terms ⟧Terms ρ = ⟦ s ⟧Term ρ • ⟦ terms ⟧Terms ρ
  
  meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
  meaningOfTerm = meaning ⟦_⟧Term

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
