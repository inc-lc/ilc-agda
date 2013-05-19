module Natural.Lookup where

-- LOOKUP values in environments
--
-- This module defines lookup of (syntactic) values in
-- (syntactic) environments as a derivation system.

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Closures

infixr 8 _⊢_↦_

data _⊢_↦_ : ∀ {Γ τ} → Env Γ → Var Γ τ → Val τ → Set where
  this : ∀ {Γ τ} {ρ : Env Γ} {v : Val τ} →
    v • ρ ⊢ this ↦ v
  that : ∀ {Γ τ₁ τ₂ x} {ρ : Env Γ} {v₁ : Val τ₁} {v₂ : Val τ₂} →
    ρ ⊢ x ↦ v₂ →
    v₁ • ρ ⊢ that x ↦ v₂
