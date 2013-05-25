module Syntactic.ChangeTypes.ChangesAreDerivatives where

-- CHANGE TYPES

-- In this calculus, changes are derivatives, hence the types of
-- changes is the same.

open import Syntactic.Types

Δ-Type : Type → Type
Δ-Type (τ₁ ⇒ τ₂) = τ₁ ⇒ Δ-Type τ₁ ⇒ Δ-Type τ₂
Δ-Type (bool) = bool -- true means negate, false means nil change
