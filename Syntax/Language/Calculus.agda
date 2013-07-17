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
open import Syntax.Language.Base public
open import Syntax.Language.Typing public

Δprimitive : ∀ {L} → Typing L → Set
Δprimitive {L} T = ∀ {Γ} → (c : Base.const L) →
  Term {T = T} Γ (Δtype T (type-of T c))

record Calculus : Set₁ where
  constructor
    calculus-with
  field
    L : Base
    T : Typing L
    Δ : Δprimitive T

-- assemble-calculus : lorem ipsum → Calculus

