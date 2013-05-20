module Syntactic.Contexts
    (Type : Set)
  where

-- CONTEXTS
--
-- This module defines the syntax of contexts, prefixes of
-- contexts and variables and properties of these notions.
--
-- This module is parametric in the syntax of types, so it
-- can be reused for different calculi.

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- TYPING CONTEXTS

-- Syntax

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

infixr 9 _•_

-- Specialized congruence rules

⟨∅⟩ : ∅ ≡ ∅
⟨∅⟩ = refl

_⟨•⟩_ : ∀ {τ₁ τ₂ Γ₁ Γ₂} → τ₁ ≡ τ₂ → Γ₁ ≡ Γ₂ → τ₁ • Γ₁ ≡ τ₂ • Γ₂
_⟨•⟩_ = cong₂ _•_

-- VARIABLES

-- Syntax

data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ

-- WEAKENING

-- CONTEXT PREFIXES
--
-- Useful for making lemmas strong enough to prove by induction.
--
-- Consider using the Subcontexts module instead.

module Prefixes where

-- Prefix of a context

  data Prefix : Context → Set where
    ∅ : ∀ {Γ} → Prefix Γ
    _•_ : ∀ {Γ} → (τ : Type) → Prefix Γ → Prefix (τ • Γ)

-- take only the prefix of a context

  take : (Γ : Context) → Prefix Γ → Context
  take Γ ∅ = ∅
  take (τ • Γ) (.τ • Γ′) = τ • take Γ Γ′

-- drop the prefix of a context

  drop : (Γ : Context) → Prefix Γ → Context
  drop Γ ∅ = Γ
  drop (τ • Γ) (.τ • Γ′) = drop Γ Γ′

-- Extend a context to a super context

  infixr 10 _⋎_

  _⋎_ : (Γ₁ Γ₂ : Context) → Context
  ∅ ⋎ Γ₂ = Γ₂
  (τ • Γ₁) ⋎ Γ₂ = τ • (Γ₁ ⋎ Γ₂)

  take-drop : ∀ Γ Γ′ → take Γ Γ′ ⋎ drop Γ Γ′ ≡ Γ
  take-drop ∅ ∅ = refl
  take-drop (τ • Γ) ∅ = refl
  take-drop (τ • Γ) (.τ • Γ′) rewrite take-drop Γ Γ′ = refl

  or-unit : ∀ Γ → Γ ⋎ ∅ ≡ Γ
  or-unit ∅ = refl
  or-unit (τ • Γ) rewrite or-unit Γ = refl

  move-prefix : ∀ Γ τ Γ′ →
    Γ ⋎ (τ • Γ′) ≡ (Γ ⋎ (τ • ∅)) ⋎ Γ′
  move-prefix ∅ τ Γ′ = refl
  move-prefix (τ • Γ) τ₁ ∅ = sym (or-unit (τ • Γ ⋎ (τ₁ • ∅)))
  move-prefix (τ • Γ) τ₁ (τ₂ • Γ′) rewrite move-prefix Γ τ₁ (τ₂ • Γ′) = refl

-- Lift a variable to a super context

  lift : ∀ {Γ₁ Γ₂ Γ₃ τ} → Var (Γ₁ ⋎ Γ₃) τ → Var (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
  lift {∅} {∅} x = x
  lift {∅} {τ • Γ₂} x = that (lift {∅} {Γ₂} x)
  lift {τ • Γ₁} {Γ₂} this = this
  lift {τ • Γ₁} {Γ₂} (that x) = that (lift {Γ₁} {Γ₂} x)

-- SUBCONTEXTS
--
-- Useful as a reified weakening operation,
-- and for making theorems strong enough to prove by induction.
--
-- The contents of this module are currently exported at the end
-- of this file.

module Subcontexts where
  infix 8 _≼_

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

  lift : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
  lift (keep τ • ≼₁) this = this
  lift (keep τ • ≼₁) (that x) = that (lift ≼₁ x)
  lift (drop τ • ≼₁) x = that (lift ≼₁ x)

-- Currently, we export the subcontext relation as well as the
-- definition of _⋎_.

open Subcontexts public
open Prefixes public using (_⋎_)
