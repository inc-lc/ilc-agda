module Theorem.IrrelevanceUnique-Popl14 where

-- Theorem IrrelevanceUnique-Popl14.
-- Every two irrelevance proofs in Calculus Popl14 are identical.

open import Property.Uniqueness public

open import Relation.Binary.PropositionalEquality
open import Denotation.Environment.Popl14
open import Theorem.EqualityReflection
open import Theorem.ProductUnique

-- Irrelevance proofs are uniq
irrelevant-uniq : ∀ {Γ} {S : Vars Γ} {ρ : ΔEnv Γ} →
  uniq (irrelevant S ρ)
irrelevant-uniq {S = ∅} {∅} = refl
irrelevant-uniq {S = lack S} = irrelevant-uniq {S = S}
irrelevant-uniq {S = have S} = Σ-uniq ≡-uniq (irrelevant-uniq {S = S})
