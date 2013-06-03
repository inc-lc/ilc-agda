module Denotational.Environments
    (Type : Set)
    {ℓ}
    (⟦_⟧Type : Type → Set ℓ)
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

open import Relation.Binary.PropositionalEquality

open import Syntactic.Contexts Type
open import Denotational.Notation

private
  meaningOfType : Meaning Type
  meaningOfType = meaning ⟦_⟧Type

-- TYPING CONTEXTS

-- Denotational Semantics : Contexts Represent Environments

data Empty : Set ℓ where
  ∅ : Empty

data Bind A B : Set ℓ where
  _•_ : (v : A) (ρ : B) → Bind A B

⟦_⟧Context : Context → Set ℓ
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

⟦_⟧≼ : ∀ {Γ₁ Γ₂} → (Γ′ : Γ₁ ≼ Γ₂) → ⟦ Γ₂ ⟧ → ⟦ Γ₁ ⟧
⟦ ∅ ⟧≼ ∅ = ∅
⟦ keep τ • Γ′ ⟧≼ (v • ρ) = v • ⟦ Γ′ ⟧≼ ρ
⟦ drop τ • Γ′ ⟧≼ (v • ρ) = ⟦ Γ′ ⟧≼ ρ

meaningOf≼ : ∀ {Γ₁ Γ₂} → Meaning (Γ₁ ≼ Γ₂)
meaningOf≼ = meaning ⟦_⟧≼

-- Properties

⟦⟧-≼-trans : ∀ {Γ₃ Γ₁ Γ₂} → (Γ′ : Γ₁ ≼ Γ₂) (Γ″ : Γ₂ ≼ Γ₃) →
  ∀ (ρ : ⟦ Γ₃ ⟧) → ⟦ ≼-trans Γ′ Γ″ ⟧ ρ ≡ ⟦ Γ′ ⟧ (⟦ Γ″ ⟧ ρ)
⟦⟧-≼-trans Γ′ ∅ ∅ = refl
⟦⟧-≼-trans (keep τ • Γ′) (keep .τ • Γ″) (v • ρ) = cong₂ _•_ refl (⟦⟧-≼-trans Γ′ Γ″ ρ)
⟦⟧-≼-trans (drop τ • Γ′) (keep .τ • Γ″) (v • ρ) = ⟦⟧-≼-trans Γ′ Γ″ ρ
⟦⟧-≼-trans Γ′ (drop τ • Γ″) (v • ρ) = ⟦⟧-≼-trans Γ′ Γ″ ρ

⟦⟧-≼-refl : ∀ {Γ : Context} →
  ∀ (ρ : ⟦ Γ ⟧) → ⟦ ≼-refl ⟧ ρ ≡ ρ
⟦⟧-≼-refl {∅} ∅ = refl
⟦⟧-≼-refl {τ • Γ} (v • ρ) = cong₂ _•_ refl (⟦⟧-≼-refl ρ)

-- SOUNDNESS of variable lifting

lift-sound : ∀ {Γ₁ Γ₂ τ} (Γ′ : Γ₁ ≼ Γ₂) (x : Var Γ₁ τ) →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ lift Γ′ x ⟧ ρ ≡ ⟦ x ⟧ (⟦ Γ′ ⟧ ρ)
lift-sound ∅ () ρ
lift-sound (keep τ • Γ′) this (v • ρ) = refl
lift-sound (keep τ • Γ′) (that x) (v • ρ) = lift-sound Γ′ x ρ
lift-sound (drop τ • Γ′) this (v • ρ) = lift-sound Γ′ this ρ
lift-sound (drop τ • Γ′) (that x) (v • ρ) = lift-sound Γ′ (that x) ρ
