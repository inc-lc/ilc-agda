------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Correctness of differentiation with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Correctness where

-- The denotational properties of the `derive` transformation
-- for Calculus Nehemiah. In particular, the main theorem
-- about it producing the correct incremental behavior.

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Denotation.Value
open import Nehemiah.Denotation.Evaluation
open import Nehemiah.Change.Type
open import Nehemiah.Change.Term
open import Nehemiah.Change.Value
open import Nehemiah.Change.Evaluation
open import Nehemiah.Change.Validity
open import Nehemiah.Change.Derive
open import Nehemiah.Change.Specification
open import Nehemiah.Change.Implementation

open import Base.Denotation.Notation
open import Relation.Binary.PropositionalEquality
open import Data.Integer
open import Structure.Bag.Nehemiah
open import Postulate.Extensionality

import Parametric.Change.Correctness
  Const ⟦_⟧Base ⟦_⟧Const ΔBase
  apply-base diff-base nil-base
  ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧
  meaning-⊕-base meaning-⊝-base meaning-onil-base
  specification-structure
  deriveConst implementation-structure as Correctness

derive-const-correct : Correctness.Structure
derive-const-correct (intlit-const n) = refl
derive-const-correct add-const w Δw .Δw refl w₁ Δw₁ .Δw₁ refl = refl
derive-const-correct minus-const w Δw .Δw refl = refl
derive-const-correct empty-const = refl
derive-const-correct insert-const w Δw .Δw refl w₁ Δw₁ .Δw₁ refl = refl
derive-const-correct union-const w Δw .Δw refl w₁ Δw₁ .Δw₁ refl = refl
derive-const-correct negate-const w Δw .Δw refl = refl
derive-const-correct flatmap-const w Δw Δw′ Δw≈Δw′ w₁ Δw₁ .Δw₁ refl =
  cong (λ □ → flatmapBag □ (w₁ ++ Δw₁) ++ negateBag (flatmapBag w w₁))
  (ext (λ n → cong (_++_ (w n)) (Δw≈Δw′ n (+ 0) (+ 0) refl)))
derive-const-correct sum-const w Δw .Δw refl = refl

open Correctness.Structure derive-const-correct public
