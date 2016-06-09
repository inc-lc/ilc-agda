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
derive-const-correct (intlit-const n) ∅ ρ dρ ρ′ dρ≈ρ′ ∅ = refl
derive-const-correct add-const (s • t • ∅) ρ dρ ρ′ dρ≈ρ′ (s-correct • t-correct • ∅) = cong₂ _+_
  s-correct
  t-correct
derive-const-correct minus-const (t • ∅) ρ dρ ρ′ dρ≈ρ′ (t-correct • ∅) =
  cong -_ t-correct
derive-const-correct empty-const ∅ ρ dρ ρ′ dρ≈ρ′ ∅ = refl
derive-const-correct insert-const (s • t • ∅) ρ dρ ρ′ dρ≈ρ′ (s-correct • t-correct • ∅) =
  cong₂ _\\_
    (cong₂ _++_
      (cong singletonBag (cong₂ _+_
        (⟦fit⟧ s ρ ρ′)
        s-correct))
      (cong₂ _++_
        (⟦fit⟧ t ρ ρ′)
        t-correct))
    (cong₂ _++_ (cong singletonBag (⟦fit⟧ s ρ ρ′)) (⟦fit⟧ t ρ ρ′))
derive-const-correct union-const (s • t • ∅) ρ dρ ρ′ dρ≈ρ′ (s-correct • t-correct • ∅) = cong₂ _++_
  s-correct
  t-correct
derive-const-correct negate-const  (t • ∅) ρ dρ ρ′ dρ≈ρ′ (t-correct • ∅) =
  cong negateBag t-correct
derive-const-correct flatmap-const (s • t • ∅) ρ dρ ρ′ dρ≈ρ′ (s-correct • t-correct • ∅) =
  cong₂ _\\_
    (cong₂ flatmapBag
      (ext (λ v →
        cong₂ _++_
          (cong (λ hole → hole v) (⟦fit⟧ s ρ ρ′))
            (s-correct v (nil₍ int ₎ v) (+ 0) refl)))
      (cong₂ _++_
        (⟦fit⟧ t ρ ρ′)
       t-correct))
    (cong₂ flatmapBag (⟦fit⟧ s ρ ρ′) (⟦fit⟧ t ρ ρ′))
derive-const-correct sum-const (t • ∅) ρ dρ ρ′ dρ≈ρ′ (t-correct • ∅) =
  cong sumBag t-correct

open Correctness.Structure derive-const-correct public
