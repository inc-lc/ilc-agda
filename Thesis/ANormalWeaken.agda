module Thesis.ANormalWeaken where

open import Relation.Binary.PropositionalEquality
open import Thesis.ANormal public

weaken-term : ∀ {Γ₁ Γ₂ τ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Term Γ₁ τ →
  Term Γ₂ τ
weaken-term Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
weaken-term Γ₁≼Γ₂ (lett f x t) = lett (weaken-var Γ₁≼Γ₂ f) (weaken-var Γ₁≼Γ₂ x) (weaken-term (keep _ • Γ₁≼Γ₂) t)

weaken-term-sound : ∀ {Γ₁ Γ₂ τ} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂)
  (t : Term Γ₁ τ) (ρ : ⟦ Γ₂ ⟧Context) → ⟦ weaken-term Γ₁≼Γ₂ t ⟧Term ρ ≡ ⟦ t ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
weaken-term-sound Γ₁≼Γ₂ (var x) ρ = weaken-var-sound Γ₁≼Γ₂ x ρ
weaken-term-sound Γ₁≼Γ₂ (lett f x t) ρ rewrite
  weaken-var-sound Γ₁≼Γ₂ f ρ | weaken-var-sound Γ₁≼Γ₂ x ρ =
    weaken-term-sound
      (keep _ • Γ₁≼Γ₂)
      t
      (⟦ f ⟧Var (⟦ Γ₁≼Γ₂ ⟧≼ ρ) (⟦ x ⟧Var (⟦ Γ₁≼Γ₂ ⟧≼ ρ)) • ρ)

weaken-fun : ∀ {Γ₁ Γ₂ τ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Fun Γ₁ τ →
  Fun Γ₂ τ
weaken-fun Γ₁≼Γ₂ (term x) = term (weaken-term Γ₁≼Γ₂ x)
weaken-fun Γ₁≼Γ₂ (abs f) = abs (weaken-fun (keep _ • Γ₁≼Γ₂) f)

open import Postulate.Extensionality

weaken-fun-sound : ∀ {Γ₁ Γ₂ τ} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂)
  (t : Fun Γ₁ τ) (ρ : ⟦ Γ₂ ⟧Context) → ⟦ weaken-fun Γ₁≼Γ₂ t ⟧Fun ρ ≡ ⟦ t ⟧Fun (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
weaken-fun-sound Γ₁≼Γ₂ (term x) ρ = weaken-term-sound Γ₁≼Γ₂ x ρ
weaken-fun-sound Γ₁≼Γ₂ (abs f) ρ = ext (λ v → weaken-fun-sound (keep _ • Γ₁≼Γ₂) f (v • ρ))
