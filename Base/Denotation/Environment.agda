------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Environments
--
-- This module defines the meaning of contexts, that is,
-- the type of environments that fit a context, together
-- with operations and properties of these operations.
--
-- This module is parametric in the syntax and semantics
-- of types, so it can be reused for different calculi
-- and models.
------------------------------------------------------------------------

module Base.Denotation.Environment
    (Type : Set)
    {ℓ}
    (⟦_⟧Type : Type → Set ℓ)
  where

open import Relation.Binary.PropositionalEquality

open import Base.Syntax.Context Type
open import Base.Denotation.Notation
import Base.Data.DependentList as DependentList

open DependentList public using (∅ ; _•_)
open DependentList

private
  meaningOfType : Meaning Type
  meaningOfType = meaning ⟦_⟧Type

⟦_⟧Context : Context → Set ℓ
⟦_⟧Context = DependentList ⟦_⟧Type

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

weaken-var-sound : ∀ {Γ₁ Γ₂ τ} (Γ′ : Γ₁ ≼ Γ₂) (x : Var Γ₁ τ) →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken-var Γ′ x ⟧ ρ ≡ ⟦ x ⟧ (⟦ Γ′ ⟧ ρ)
weaken-var-sound ∅ () ρ
weaken-var-sound (keep τ • Γ′) this (v • ρ) = refl
weaken-var-sound (keep τ • Γ′) (that x) (v • ρ) = weaken-var-sound Γ′ x ρ
weaken-var-sound (drop τ • Γ′) this (v • ρ) = weaken-var-sound Γ′ this ρ
weaken-var-sound (drop τ • Γ′) (that x) (v • ρ) = weaken-var-sound Γ′ (that x) ρ
