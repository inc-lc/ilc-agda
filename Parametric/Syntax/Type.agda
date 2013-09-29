module Parametric.Syntax.Type where

-- Types for language description à la Plotkin (LCF as PL)
--
-- Given base types, we build function types.

Structure : Set₁
Structure = Set

module Structure (Base : Structure) where
  infixr 5 _⇒_

  data Type : Set where
    base : (ι : Base) → Type
    _⇒_ : (σ : Type) → (τ : Type) → Type

  open import Base.Syntax.Context Type public
  open import Base.Syntax.Vars Type public

  -- Internalize a context to a type.
  --
  -- Is there a better name for this function?
  internalizeContext : (Σ : Context) (τ′ : Type) → Type
  internalizeContext ∅ τ′ = τ′
  internalizeContext (τ • Σ) τ′ = τ ⇒ internalizeContext Σ τ′
