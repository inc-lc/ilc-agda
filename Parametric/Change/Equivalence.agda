------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Delta-observational equivalence
------------------------------------------------------------------------
module Parametric.Change.Equivalence where

open import Base.Denotation.Notation public

open import Relation.Binary.PropositionalEquality
open import Base.Change.Algebra
open import Level
open import Data.Unit

-- Extension Point: None (currently). Do we need to allow plugins to customize
-- this concept?
Structure : Set
Structure = Unit

module Structure (unused : Structure) where

  module _ {a ℓ} {A : Set a} {{ca : ChangeAlgebra ℓ A}} {x : A} where
    -- Delta-observational equivalence: these asserts that two changes
    -- give the same result when applied to a base value.
    _≙_ : ∀ dx dy → Set a
    dx ≙ dy = x ⊞ dx ≡ x ⊞ dy

    -- _≙_ is indeed an equivalence relation:
    ≙-refl : ∀ {dx} → dx ≙ dx
    ≙-refl = refl

    ≙-symm : ∀ {dx dy} → dx ≙ dy → dy ≙ dx
    ≙-symm ≙ = sym ≙

    ≙-trans : ∀ {dx dy dz} → dx ≙ dy → dy ≙ dz → dx ≙ dz
    ≙-trans ≙₁ ≙₂ = trans ≙₁ ≙₂

    -- TODO: we want to show that all functions of interest respect
    -- delta-observational equivalence, so that two d.o.e. changes can be
    -- substituted for each other freely. That should be true for functions
    -- using changes parametrically, for derivatives and function changes, and
    -- for functions using only the interface to changes (including the fact
    -- that function changes are functions). Stating the general result, though,
    -- seems hard, we should rather have lemmas proving that certain classes of
    -- functions respect this equivalence.
