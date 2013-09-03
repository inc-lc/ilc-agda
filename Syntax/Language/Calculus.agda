module Syntax.Language.Calculus where

-- Full description of a calculus in Plotkin style
--
-- Users should supply
-- - base types
-- - constants
-- - Δtype of base types
-- - derivatives of constants

open import Syntax.Type.Plotkin public
open import Syntax.Term.Plotkin public
open import Syntax.Context public
open import Syntax.Context.Plotkin public
open import Syntax.DeltaContext public

record Calculus : Set₁ where
  constructor
    calculus-with
  field
    basetype : Set
    constant : Context {Type basetype} → Type basetype → Set
    Δtype : Type basetype → Type basetype
    Δconst : ∀ {Γ Σ τ} → (c : constant Σ τ) →
      Term {basetype} {constant} Γ
        (internalizeContext basetype (ΔContext′ (Type basetype) Δtype Σ) (Δtype τ))

open Calculus public

type : Calculus → Set
type L = Type (basetype L)

context : Calculus → Set
context L = Context {type L}

term : (L : Calculus) → context L → type L → Set
term L = Term {basetype L} {constant L}
