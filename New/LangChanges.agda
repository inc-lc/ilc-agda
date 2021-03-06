module New.LangChanges where

open import New.Lang public
open import New.Changes

isChAlgτ : (τ : Type) → IsChAlg ⟦ τ ⟧Type ⟦ Δt τ ⟧Type

Chτ : (τ : Type) → Set
Chτ τ = ⟦ Δt τ ⟧Type

chAlgt : (τ : Type) → ChAlg ⟦ τ ⟧Type
chAlgt τ = record { Ch = Chτ τ ; isChAlg = isChAlgτ τ}

instance
  ichAlgt : ∀ {τ} → ChAlg ⟦ τ ⟧Type
  ichAlgt {τ} = chAlgt τ

isChAlgτ (σ ⇒ τ) = isChAlg {{funCA {{chAlgt σ}} {{chAlgt τ}}}}
isChAlgτ int = isChAlg {{intCA}}
isChAlgτ (pair σ τ) = isChAlg {{pairCA {{chAlgt σ}} {{chAlgt τ}}}}
isChAlgτ (sum σ τ) = isChAlg {{sumCA {{chAlgt σ}} {{chAlgt τ}}}}

ΔΓ : Context → Context
ΔΓ ∅ = ∅
ΔΓ (τ • Γ) = Δt τ • τ • ΔΓ Γ

module _ where
  ChΓ : ∀ (Γ : Context) → Set
  ChΓ Γ = ⟦ ΔΓ Γ ⟧Context

  _e⊕_ : ∀ {Γ} → ⟦ Γ ⟧Context → ChΓ Γ → ⟦ Γ ⟧Context
  _e⊕_ ∅ ∅ = ∅
  _e⊕_ (v • ρ) (dv • _ • dρ) = v ⊕ dv • ρ e⊕ dρ
  _e⊝_ : ∀ {Γ} → ⟦ Γ ⟧Context → ⟦ Γ ⟧Context → ChΓ Γ
  _e⊝_ ∅ ∅ = ∅
  _e⊝_ (v₂ • ρ₂) (v₁ • ρ₁) = v₂ ⊝ v₁ • v₁ • ρ₂ e⊝ ρ₁

  validΓ : ∀ {Γ} → ⟦ Γ ⟧Context → ChΓ Γ → Set
  validΓ ∅ ∅ = ⊤
  validΓ (v • ρ) (dv • v′ • dρ) = valid v dv × v ≡ v′ × validΓ ρ dρ

  e⊝-valid : ∀ {Γ} → (ρ1 ρ2 : ⟦ Γ ⟧Context) → validΓ ρ1 (ρ2 e⊝ ρ1)
  e⊝-valid ∅ ∅ = tt
  e⊝-valid (v₁ • ρ₁) (v₂ • ρ₂) = ⊝-valid v₁ v₂ , refl , e⊝-valid ρ₁ ρ₂
  e⊕-⊝ : ∀ {Γ} → (ρ2 ρ1 : ⟦ Γ ⟧Context) → ρ1 e⊕ (ρ2 e⊝ ρ1) ≡ ρ2
  e⊕-⊝ ∅ ∅ = refl
  e⊕-⊝ (v₂ • ρ₂) (v₁ • ρ₁) = cong₂ _•_ (⊕-⊝ v₂ v₁) (e⊕-⊝ ρ₂ ρ₁)

  {-# TERMINATING #-}
  isEnvCA : ∀ Γ → IsChAlg ⟦ Γ ⟧Context (ChΓ Γ)

  e⊚-valid : ∀ {Γ} → (ρ : ⟦ Γ ⟧Context) (dρ1 : ChΓ Γ) →
      validΓ ρ dρ1 →
      (dρ2 : ChΓ Γ) →
      validΓ (ρ e⊕ dρ1) dρ2 →
      validΓ ρ (IsChAlg.default-⊚ (isEnvCA Γ) dρ1 ρ dρ2)
  e⊚-correct : ∀ {Γ} → (ρ : ⟦ Γ ⟧Context) (dρ1 : ChΓ Γ) →
      validΓ ρ dρ1 →
      (dρ2 : ChΓ Γ) →
      validΓ (ρ e⊕ dρ1) dρ2 →
      (ρ e⊕ IsChAlg.default-⊚ (isEnvCA Γ) dρ1 ρ dρ2) ≡
      ((ρ e⊕ dρ1) e⊕ dρ2)

  isEnvCA Γ = record
    { _⊕_ = _e⊕_
    ; _⊝_ = _e⊝_
    ; valid = validΓ
    ; ⊝-valid = e⊝-valid
    ; ⊕-⊝ = e⊕-⊝
    ; _⊚[_]_ = IsChAlg.default-⊚ (isEnvCA Γ)
    ; ⊚-valid = e⊚-valid
    ; ⊚-correct = e⊚-correct
    }
  e⊚-valid {Γ} = IsChAlg.default-⊚-valid (isEnvCA Γ)
  e⊚-correct {Γ} = IsChAlg.default-⊚-correct (isEnvCA Γ)

  envCA : ∀ Γ → ChAlg ⟦ Γ ⟧Context
  envCA Γ = record
    { Ch = ChΓ Γ
    ; isChAlg = isEnvCA Γ }

instance
  ienvCA : ∀ {Γ} → ChAlg ⟦ Γ ⟧Context
  ienvCA {Γ} = envCA Γ
