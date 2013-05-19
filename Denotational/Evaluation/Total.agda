module Denotational.Evaluation.Total where

-- EVALUATION with a primitive for TOTAL DERIVATIVES
--
-- This module defines the semantics of terms that support a
-- primitive (Δ e) for computing the total derivative according
-- to all free variables in e and all future arguments of e if e
-- is a function.

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type

open import Changes
open import ChangeContexts

-- TERMS

-- Denotational Semantics

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ app t₁ t₂ ⟧Term ρ = (⟦ t₁ ⟧Term ρ) (⟦ t₂ ⟧Term ρ)
⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
⟦ true ⟧Term ρ = true
⟦ false ⟧Term ρ = false
⟦ if t₁ t₂ t₃ ⟧Term ρ with ⟦ t₁ ⟧Term ρ
... | true = ⟦ t₂ ⟧Term ρ
... | false = ⟦ t₃ ⟧Term ρ
⟦ Δ t ⟧Term ρ = diff (⟦ t ⟧Term (update ρ)) (⟦ t ⟧Term (ignore ρ))
⟦ weakenOne Γ₁ τ₂ t ⟧Term ρ = ⟦ t ⟧Term (weakenEnv Γ₁ τ₂ ρ)

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term
