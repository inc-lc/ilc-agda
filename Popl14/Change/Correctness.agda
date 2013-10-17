module Popl14.Change.Correctness where

-- The denotational properties of the `derive` transformation
-- for Calculus Popl14. In particular, the main theorem
-- about it producing the correct incremental behavior.

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value
open import Popl14.Denotation.Evaluation
open import Popl14.Change.Type
open import Popl14.Change.Term
open import Popl14.Change.Value
open import Popl14.Change.Evaluation
open import Popl14.Change.Validity
open import Popl14.Change.Derive
open import Popl14.Change.Specification
open import Popl14.Change.Implementation

open import Base.Denotation.Notation
open import Relation.Binary.PropositionalEquality
open import Data.Integer
open import Structure.Bag.Popl14
open import Postulate.Extensionality

import Parametric.Change.Correctness
  Const ⟦_⟧Base ⟦_⟧Const ΔBase
  diff-base apply-base
  ⟦apply-base⟧ ⟦diff-base⟧
  meaning-⊕-base meaning-⊝-base
  change-algebra-base-family specification-structure
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
            (s-correct v (nil-change int v) (v - v) refl)))
      (cong₂ _++_
        (⟦fit⟧ t ρ ρ′)
       t-correct))
    (cong₂ flatmapBag (⟦fit⟧ s ρ ρ′) (⟦fit⟧ t ρ ρ′))
derive-const-correct sum-const (t • ∅) ρ dρ ρ′ dρ≈ρ′ (t-correct • ∅) =
  cong sumBag t-correct

open Correctness.Structure derive-const-correct public
