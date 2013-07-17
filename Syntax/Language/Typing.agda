module Syntax.Language.Typing where

-- Typing languages described in Plotkin stype
--
-- This module belongs together with Syntax.Language.Base.
-- It is separated only to eliminate cyclic module dependency.

open import Syntax.Language.Base
open import Syntax.Type.Plotkin

record Typing (L : Base) : Set where
  constructor
    typing
  field
    lookup : Base.const L → Type (Base.type L)
    Δtype  : Base.type L → Type (Base.type L)

-- Abbreviation of typing operations

type-of : ∀ {L} → Typing L → Base.const L → Type (Base.type L)
type-of T c = Typing.lookup T c

Δtype : ∀ {L} (T : Typing L) →
  Type (Base.type L) → Type (Base.type L)
Δtype T (base ι) = Typing.Δtype T ι
Δtype T (σ ⇒ τ) = σ ⇒ Δtype T σ ⇒ Δtype T τ

lift-Δbase : ∀ {B} → (B → B) → (B → Type B)
lift-Δbase f = λ ι → base (f ι)
