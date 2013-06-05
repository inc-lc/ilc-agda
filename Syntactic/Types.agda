module Syntactic.Types where

-- SIMPLE TYPES
--
-- This module defines the syntax of simple types.

open import Function

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality

-- SIMPLE TYPES

-- Syntax

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type
  bool : Type

inv⇒₁ : ∀ {τ₁ τ₂ τ₃ τ₄} → τ₁ ⇒ τ₂ ≡ τ₃ ⇒ τ₄ → τ₁ ≡ τ₃
inv⇒₁ refl = refl

inv⇒₂ : ∀ {τ₁ τ₂ τ₃ τ₄} → τ₁ ⇒ τ₂ ≡ τ₃ ⇒ τ₄ → τ₂ ≡ τ₄
inv⇒₂ refl = refl

infixr 5 _⇒_

_≟_ : Decidable {A = Type} _≡_
(τ₁ ⇒ τ₂) ≟ (τ₃ ⇒ τ₄) with τ₁ ≟ τ₃ | τ₂ ≟ τ₄
(.τ₃ ⇒ .τ₄) ≟ (τ₃ ⇒ τ₄) | yes refl | yes refl = yes refl
(.τ₃ ⇒ τ₂) ≟ (τ₃ ⇒ τ₄) | yes refl | no ¬p = no (¬p ∘ inv⇒₂)
(τ₁ ⇒ .τ₄) ≟ (τ₃ ⇒ τ₄) | no ¬p | yes refl = no (¬p ∘ inv⇒₁)
(τ₁ ⇒ τ₂) ≟ (τ₃ ⇒ τ₄) | no ¬p | no ¬p₁ = no (¬p ∘ inv⇒₁)
(τ₁ ⇒ τ₂) ≟ bool = no λ ()
bool ≟ (τ₂ ⇒ τ₃) = no λ ()
bool ≟ bool = yes refl
