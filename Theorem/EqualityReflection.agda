module Theorem.EqualityReflection where

-- Hofmann [1] states that intensional type theory plus
-- extensionality postulate plus equality reflection equals
-- extensional type theory.
--
-- However, "equality reflection" is a theorem in Agda.
-- Either we are reasoning within extensional type theory
-- (an acceptable deed) or Agda plus extensionality is
-- somehow stronger than ITT plus extensionality (less
-- savory).
--
-- [1]: M. Hofmann. Conservativity of equality reflection
-- over intensional type theory. LNCS 1158 pp. 153--164.

open import Property.Uniqueness public

open import Relation.Binary.PropositionalEquality

-- Equivalence proofs are unique
≡-uniq : ∀ {A : Set} {a b : A} → uniq (a ≡ b)
≡-uniq = proof where -- Boilerplate
  proof : ∀ {A : Set} {a b : A} → ∀ {p q : a ≡ b} → p ≡ q
  proof {p = refl} {refl} = refl
