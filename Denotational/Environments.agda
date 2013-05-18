module Denotational.Environments
    (Type : Set)
    (⟦_⟧Type : Type → Set)
  where

-- ENVIRONMENTS
--
-- This module defines the meaning of contexts, that is,
-- the type of environments that fit a context, together
-- with operations and properties of these operations.
--
-- This module is parametric in the syntax and semantics
-- of types, so it can be reused for different calculi
-- and models.

open import Syntactic.Contexts Type
open import Denotational.Notation

private
  meaningOfType : Meaning Type
  meaningOfType = meaning ⟦_⟧Type

-- TYPING CONTEXTS

-- Denotational Semantics : Contexts Represent Environments

data Empty : Set where
  ∅ : Empty

data Bind A B : Set where
  _•_ : (v : A) (ρ : B) → Bind A B

⟦_⟧Context : Context → Set
⟦ ∅ ⟧Context = Empty
⟦ τ • Γ ⟧Context = Bind ⟦ τ ⟧ ⟦ Γ ⟧Context

meaningOfContext : Meaning Context
meaningOfContext = meaning ⟦_⟧Context

-- VARIABLES

-- Denotational Semantics

⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ this ⟧Var (v • ρ) = v
⟦ that x ⟧Var (v • ρ) = ⟦ x ⟧Var ρ

meaningOfVar : ∀ {Γ τ} → Meaning (Var Γ τ)
meaningOfVar = meaning ⟦_⟧Var

-- WEAKENING

-- Remove a variable from an environment

weakenEnv : ∀ Γ₁ τ₂ {Γ₃} → ⟦ Γ₁ ⋎ (τ₂ • Γ₃) ⟧ → ⟦ Γ₁ ⋎ Γ₃ ⟧
weakenEnv ∅ τ₂ (v • ρ) = ρ
weakenEnv (τ • Γ₁) τ₂ (v • ρ) = v • weakenEnv Γ₁ τ₂ ρ
