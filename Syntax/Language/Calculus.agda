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
open import Syntax.Context.Plotkin public

record Calculus : Set₁ where
  constructor
    calculus-with
  field
    basetype : Set
    constant : Set
    type-of : constant → Type basetype
    Δtype : Type basetype → Type basetype
    Δconst : ∀ {Γ} → (c : constant) →
      Term {basetype} {constant} {type-of} Γ (Δtype (type-of c))

open Calculus public

type : Calculus → Set
type L = Type (basetype L)

context : Calculus → Set
context L = Context {type L}

term : (L : Calculus) → context L → type L → Set
term L = Term {basetype L} {constant L} {type-of L}
