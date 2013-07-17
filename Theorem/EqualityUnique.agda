module Theorem.EqualityUnique where

open import Property.Uniqueness public

open import Relation.Binary.PropositionalEquality

-- Equivalence proofs are unique
≡-uniq : ∀ {A : Set} {a b : A} → uniq (a ≡ b)
≡-uniq = proof where -- Boilerplate
  proof : ∀ {A : Set} {a b : A} → ∀ {p q : a ≡ b} → p ≡ q
  proof {p = p} {q} = proof-irrelevance p q
