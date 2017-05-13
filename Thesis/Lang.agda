module Thesis.Lang where

open import Thesis.Syntax public
open import Thesis.Environments public

⟦_⟧Const : ∀ {τ} → Const τ → ⟦ τ ⟧Type
⟦ lit n ⟧Const = n
⟦ plus ⟧Const = _+_
⟦ minus ⟧Const = _-_
⟦ cons ⟧Const v1 v2 = v1 , v2
⟦ fst ⟧Const (v1 , v2) = v1
⟦ snd ⟧Const (v1 , v2) = v2
⟦ linj ⟧Const v1 = inj₁ v1
⟦ rinj ⟧Const v2 = inj₂ v2
⟦ match ⟧Const (inj₁ x) f g = f x
⟦ match ⟧Const (inj₂ y) f g = g y

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ const c ⟧Term ρ = ⟦ c ⟧Const
⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
⟦ app s t ⟧Term ρ = ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ)
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)

open import Theorem.CongApp
open import Postulate.Extensionality

weaken-sound : ∀ {Γ₁ Γ₂ τ} {Γ₁≼Γ₂ : Γ₁ ≼ Γ₂}
  (t : Term Γ₁ τ) (ρ : ⟦ Γ₂ ⟧Context) → ⟦ weaken Γ₁≼Γ₂ t ⟧Term ρ ≡ ⟦ t ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
weaken-sound {Γ₁≼Γ₂ = Γ₁≼Γ₂} (var x) ρ = weaken-var-sound Γ₁≼Γ₂ x ρ
weaken-sound (app s t) ρ = weaken-sound s ρ ⟨$⟩ weaken-sound t ρ
weaken-sound (abs t) ρ = ext (λ v → weaken-sound t (v • ρ))
weaken-sound (const c) ρ = refl
