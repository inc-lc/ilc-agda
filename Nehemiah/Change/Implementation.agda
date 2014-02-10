------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Logical relation for erasure with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Implementation where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Denotation.Value
open import Nehemiah.Denotation.Evaluation
open import Nehemiah.Change.Validity
open import Nehemiah.Change.Specification
open import Nehemiah.Change.Type
open import Nehemiah.Change.Value
open import Nehemiah.Change.Derive

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Integer
open import Structure.Bag.Nehemiah

import Parametric.Change.Implementation
    Const ⟦_⟧Base ⟦_⟧Const ΔBase
    change-algebra-base-family specification-structure
    ⟦apply-base⟧ ⟦diff-base⟧ deriveConst as Implementation

private
  implements-base : ∀ ι {v : ⟦ ι ⟧Base} → Δ₍ ι ₎ v → ⟦ ΔBase ι ⟧Base → Set
  implements-base base-int {v} Δv Δv′ = Δv ≡ Δv′
  implements-base base-bag {v} Δv Δv′ = Δv ≡ Δv′

  u⊟v≈u⊝v-base : ∀ ι → {u v : ⟦ ι ⟧Base} →
      implements-base ι {v} (u ⊟₍ ι ₎ v) (⟦diff-base⟧ ι u v)
  u⊟v≈u⊝v-base base-int = refl
  u⊟v≈u⊝v-base base-bag = refl

  carry-over-base : ∀ {ι}
    {v : ⟦ ι ⟧Base}
    (Δv : Δ₍ ι ₎ v)
    {Δv′ : ⟦ ΔBase ι ⟧Base} (Δv≈Δv′ : implements-base ι {v} Δv Δv′) →
      v ⊞₍ base ι ₎ Δv ≡ v ⟦⊕₍ base ι ₎⟧ Δv′
  carry-over-base {base-int} {v} Δv Δv≈Δv′ = cong (_+_ v) Δv≈Δv′
  carry-over-base {base-bag} Δv Δv≈Δv′ = cong (_++_ (before₍ bag ₎ Δv)) Δv≈Δv′

implementation-structure : Implementation.Structure
implementation-structure = record
    { implements-base = implements-base
    ; u⊟v≈u⊝v-base = u⊟v≈u⊝v-base
    ; carry-over-base = carry-over-base
    }

open Implementation.Structure implementation-structure public
