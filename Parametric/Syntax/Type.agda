module Parametric.Syntax.Type
  (Base : Set)
  where

-- Types for language description à la Plotkin (LCF as PL)
--
-- Given base types, we build function types.

infixr 5 _⇒_

data Type : Set where
  base : (ι : Base) → Type
  _⇒_ : (σ : Type) → (τ : Type) → Type

open import Base.Syntax.Context Type

-- Internalize a context to a type.
--
-- Is there a better name for this function?
internalizeContext : (Σ : Context) (τ′ : Type) → Type
internalizeContext ∅ τ′ = τ′
internalizeContext (τ • Σ) τ′ = τ ⇒ internalizeContext Σ τ′
