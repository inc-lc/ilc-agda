module Theorem.ValidityUnique-Popl14 where

-- Theorem IrrelevanceUnique-Popl14.
-- Every two irrelevance proofs in Calculus Popl14 are identical.

open import Property.Uniqueness public

open import Relation.Binary.PropositionalEquality
open import Denotation.Evaluation.Popl14
open import Denotation.Change.Popl14
open import Theorem.ProductUnique
open import Theorem.EqualityUnique
open import Postulate.Extensionality

-- Validity proofs are (extensionally) unique (as functions)
valid-uniq : ∀ {τ} {v : ⟦ τ ⟧} {Δv : ΔVal τ} →
  ∀ {p q : valid v Δv} → p ≡ q
valid-uniq {int} = refl
valid-uniq {bag} = refl
valid-uniq {σ ⇒ τ} =  ext³ (λ v Δv R[v,Δv] →
  Σ-uniq (valid-uniq {τ}) ≡-uniq)
