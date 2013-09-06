module Syntax.Context.Plotkin
    (Base : Set)
  where

open import Syntax.Type.Plotkin Base
open import Base.Syntax.Context Type

-- Internalize a context to a type.
--
-- Is there a better name for this function?
internalizeContext : (Σ : Context) (τ′ : Type) → Type
internalizeContext ∅ τ′ = τ′
internalizeContext (τ • Σ) τ′ = τ ⇒ internalizeContext Σ τ′
