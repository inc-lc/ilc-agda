module Theorem.ProductUnique where

-- Theorem ProductUnique.
-- The product of two sets with at most one member each is a
-- set with one or fewer members.

open import Property.Uniqueness public

open import Relation.Binary.PropositionalEquality
open import Data.Product

-- Product of singletons are singletons (for example)
Σ-uniq : ∀ {A : Set} {B : A → Set} →
  uniq A →
  (∀ {a} → uniq (B a)) →
  uniq (Σ A B)
Σ-uniq {A} {B} lhs rhs {a , c} {b , d}
  rewrite lhs {a} {b} = cong (_,_ b) rhs
