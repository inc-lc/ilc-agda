module Theorem.IrrelevanceUnique-Popl14 where

-- Theorem IrrelevanceUnique-Popl14.
-- Every two irrelevance proofs in Calculus Popl14 are identical.

open import Property.Uniqueness public

open import Relation.Binary.PropositionalEquality
open import Theorem.Irrelevance-Popl14
open import Theorem.EqualityUnique
open import Theorem.ProductUnique

-- Irrelevance proofs are uniq
irrelevant-uniq : ∀ {Γ} {S : Vars Γ} {ρ : ⟦ Γ ⟧} {dρ : Δ₍ Γ ₎ ρ} →
  uniq (irrelevant S ρ dρ)
irrelevant-uniq {S = ∅} {∅} {∅} = refl
irrelevant-uniq {S = lack S} {_ • _} {_ • _} = irrelevant-uniq {S = S}
irrelevant-uniq {S = have S} {_ • _} {_ • _} = Σ-uniq ≡-uniq (irrelevant-uniq {S = S})
