module Syntax.Language.Calculus where

-- Full description of a calculus in Plotkin style
--
-- Users should supply
-- - base types
-- - constants
-- - Δtype of base types
-- - derivatives of constants

open import Parametric.Syntax.Type public
open import Syntax.Term.Plotkin public
open import Base.Syntax.Context public
open import Syntax.Context.Plotkin public
open import Syntax.DeltaContext public

record Calculus : Set₁ where
  constructor
    calculus-with
  field
    basetype : Set
    constant : Context (Type basetype) → Type basetype → Set
    Δtype : Type basetype → Type basetype
    Δconst : ∀ {Γ Σ τ} → (c : constant Σ τ) →
      Term constant Γ
        (internalizeContext basetype (ΔContext′ Δtype Σ) (Δtype τ))

  type : Set
  type = Type basetype

  context : Set
  context = Context type

  term : context → type → Set
  term = Term constant

open Calculus public
