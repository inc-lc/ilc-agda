------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Delta-observational equivalence - support for equational reasoning
------------------------------------------------------------------------
module Base.Change.Equivalence.EqReasoning where

open import Relation.Binary.PropositionalEquality
open import Base.Change.Algebra
open import Level
open import Data.Unit
open import Function

open import Base.Change.Equivalence.Base public

module _ {a ℓ} {A : Set a} {{ca : ChangeAlgebra ℓ A}} {x : A} where
  ------------------------------------------------------------------------
  -- Convenient syntax for equational reasoning

  import Relation.Binary.EqReasoning as EqR

  module ≙-Reasoning where
    open EqR (≙-setoid {{ca}} {x = x}) public
      renaming (_≈⟨_⟩_ to _≙⟨_⟩_)
