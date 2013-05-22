module Syntactic.Closures where

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

-- NATURAL SEMANTICS

-- (without support for Δ for now)

-- Syntax

data Env : Context → Set
data Val : Type → Set

data Val where
  ⟨abs_,_⟩ : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) (ρ : Env Γ) → Val (τ₁ ⇒ τ₂)
  vtrue : Val bool
  vfalse : Val bool

data Env where
  ∅ : Env ∅
  _•_ : ∀ {Γ τ} → Val τ → Env Γ → Env (τ • Γ)
