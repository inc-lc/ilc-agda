module Syntax.Language.Calculus where

-- Full description of a calculus in Plotkin style
--
-- Users should supply
-- - base types
-- - constants
-- - Δtype of base types
-- - derivatives of constants

open import Parametric.Syntax.Type public
open import Parametric.Syntax.Term public
open import Base.Change.Context public

record Calculus : Set₁ where
  constructor
    calculus-with
  field
    basetype : Set
    constant : Context basetype → Type basetype → Set
    Δtype : Type basetype → Type basetype
    Δconst : ∀ {Γ Σ τ} → (c : constant Σ τ) →
      Term constant Γ
        (internalizeContext basetype (ΔContext′ Δtype Σ) (Δtype τ))

  type : Set
  type = Type basetype

  context : Set
  context = Context basetype

  term : context → type → Set
  term = Term constant

open Calculus public
