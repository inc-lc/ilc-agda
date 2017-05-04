------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Variables and contexts
--
-- This module defines the syntax of contexts and subcontexts,
-- together with variables and properties of these notions.
--
-- This module is parametric in the syntax of types, so it
-- can be reused for different calculi.
------------------------------------------------------------------------

module Base.Syntax.Context
    (Type : Set)
  where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- Typing Contexts
-- ===============

import Data.List as List
open import Base.Data.ContextList public

Context : Set
Context = List.List Type

-- Variables
-- =========
--
-- Here it is clear that we are using de Bruijn indices,
-- encoded as natural numbers, more or less.
data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ σ τ} → (x : Var Γ τ) → Var (σ • Γ) τ

-- Weakening
-- =========
--
-- We define weakening based on subcontext relationship.

-- Subcontexts
-- -----------
--
-- Useful as a reified weakening operation,
-- and for making theorems strong enough to prove by induction.
--
-- The contents of this module are currently exported at the end
-- of this file.

-- This handling of contexts is recommended by [this
-- email](https://lists.chalmers.se/pipermail/agda/2011/003423.html) and
-- attributed to Conor McBride.
--
-- The associated thread discusses a few alternatives solutions, including one
-- where beta-reduction can handle associativity of ++.

module Subcontexts where
  infix 4 _≼_

  data _≼_ : (Γ₁ Γ₂ : Context) → Set where
    ∅ : ∅ ≼ ∅
    keep_•_ : ∀ {Γ₁ Γ₂} →
      (τ : Type) →
      Γ₁ ≼ Γ₂ →
      τ • Γ₁ ≼ τ • Γ₂
    drop_•_ : ∀ {Γ₁ Γ₂} →
      (τ : Type) →
      Γ₁ ≼ Γ₂ →
      Γ₁ ≼ τ • Γ₂

  -- Properties

  ∅≼Γ : ∀ {Γ} → ∅ ≼ Γ
  ∅≼Γ {∅} = ∅
  ∅≼Γ {τ • Γ} = drop τ • ∅≼Γ

  ≼-refl : Reflexive _≼_
  ≼-refl {∅} = ∅
  ≼-refl {τ • Γ} = keep τ • ≼-refl

  ≼-reflexive : ∀ {Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Γ₁ ≼ Γ₂
  ≼-reflexive refl = ≼-refl

  ≼-trans : Transitive _≼_
  ≼-trans ≼₁ ∅ = ≼₁
  ≼-trans (keep .τ • ≼₁) (keep τ • ≼₂) = keep τ • ≼-trans ≼₁ ≼₂
  ≼-trans (drop .τ • ≼₁) (keep τ • ≼₂) = drop τ • ≼-trans ≼₁ ≼₂
  ≼-trans ≼₁ (drop τ • ≼₂) = drop τ • ≼-trans ≼₁ ≼₂

  ≼-isPreorder : IsPreorder _≡_ _≼_
  ≼-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = ≼-reflexive
    ; trans = ≼-trans
    }

  ≼-preorder : Preorder _ _ _
  ≼-preorder = record
    { Carrier = Context
    ; _≈_ = _≡_
    ; _∼_ = _≼_
    ; isPreorder = ≼-isPreorder
    }

  module ≼-Reasoning where
    open import Relation.Binary.PreorderReasoning ≼-preorder public
      renaming
        ( _≈⟨_⟩_ to _≡⟨_⟩_
        ; _∼⟨_⟩_ to _≼⟨_⟩_
        ; _≈⟨⟩_ to _≡⟨⟩_
        )

  -- Lift a variable to a super context

  weaken-var : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
  weaken-var (keep τ • ≼₁) this = this
  weaken-var (keep τ • ≼₁) (that x) = that (weaken-var ≼₁ x)
  weaken-var (drop τ • ≼₁) x = that (weaken-var ≼₁ x)

-- Currently, we export the subcontext relation.

open Subcontexts public
