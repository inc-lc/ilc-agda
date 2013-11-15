module Theorem.IrrelevanceUnique-Nehemiah where

-- Theorem IrrelevanceUnique-Nehemiah.
-- Every two irrelevance proofs in Calculus Nehemiah are identical.

open import Property.Uniqueness public

open import Relation.Binary.PropositionalEquality
open import Theorem.Irrelevance-Nehemiah
open import Theorem.EqualityUnique
open import Theorem.ProductUnique

-- Irrelevance proofs are uniq
irrelevant-uniq : ∀ {Γ} {S : Vars Γ} {ρ : ⟦ Γ ⟧} {dρ : Δ₍ Γ ₎ ρ} →
  uniq (irrelevant S ρ dρ)
irrelevant-uniq {S = ∅} {∅} {∅} = refl
irrelevant-uniq {S = lack S} {_ • _} {_ • _} = irrelevant-uniq {S = S}
irrelevant-uniq {S = have S} {_ • _} {_ • _} = Σ-uniq ≡-uniq (irrelevant-uniq {S = S})
