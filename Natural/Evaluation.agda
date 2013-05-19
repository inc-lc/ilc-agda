module Natural.Evaluation where

-- EVALUATION of terms to values
--
-- This module defines evaluation of syntactic terms to syntactic
-- values as a derivation system. Δ is not yet supported.

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total
open import Syntactic.Closures

open import Natural.Lookup

infixr 8 _⊢_↓_

data _⊢_↓_ : ∀ {Γ τ} → Env Γ → Term Γ τ → Val τ → Set where
  abs : ∀ {Γ τ₁ τ₂ ρ} {t : Term (τ₁ • Γ) τ₂} →
    ρ ⊢ abs t ↓ ⟨abs t , ρ ⟩
  app : ∀ {Γ Γ′ τ₁ τ₂ ρ ρ′ v₂ v′} {t₁ : Term Γ (τ₁ ⇒ τ₂)} {t₂ : Term Γ τ₁} {t′ : Term (τ₁ • Γ′) τ₂} →
    ρ ⊢ t₁ ↓ ⟨abs t′ , ρ′ ⟩ →
    ρ ⊢ t₂ ↓ v₂ →
    v₂ • ρ′ ⊢ t′ ↓ v′ →
    ρ ⊢ app t₁ t₂ ↓ v′
  var : ∀ {Γ τ x} {ρ : Env Γ} {v : Val τ}→
    ρ ⊢ x ↦ v →
    ρ ⊢ var x ↓ v
