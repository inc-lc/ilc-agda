------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Bags with negative multiplicities, for Nehemiah.
--
-- Instead of implementing bags (with negative multiplicities,
-- like in the paper) in Agda, we postulate that a group of such
-- bags exist. Note that integer bags with integer multiplicities
-- are actually the free group given a singleton operation
-- `Integer -> Bag`, so this should be easy to formalize in
-- principle.
------------------------------------------------------------------------
module Postulate.Bag-Nehemiah where

-- Postulates about bags of integers, version Nehemiah
--
-- This module postulates bags of integers with negative
-- multiplicities as a group under additive union.

open import Relation.Binary.PropositionalEquality
open import Algebra.Structures
open import Data.Integer

-- postulate Bag as an abelion group
postulate Bag : Set
-- singleton
postulate singletonBag : ℤ → Bag
-- union
postulate _++_ : Bag → Bag → Bag
infixr 5 _++_
-- negate = mapMultiplicities (λ z → - z)
postulate negateBag : Bag → Bag
postulate emptyBag : Bag
instance
  postulate abelian-bag : IsAbelianGroup _≡_ _++_ emptyBag negateBag

-- Naming convention follows Algebra.Morphism
-- Homomorphic₁ : morphism preserves negation
Homomorphic₁ :
  {A B : Set} (f : A → B) (negA : A → A) (negB : B → B) → Set
Homomorphic₁ {A} {B} f negA negB = ∀ {x} → f (negA x) ≡ negB (f x)

-- Homomorphic₂ : morphism preserves binary operation.
Homomorphic₂ :
  {A B : Set} (f : A → B) (_+_ : A → A → A) (_*_ : B → B → B) → Set
Homomorphic₂ {A} {B} f _+_ _*_ = ∀ {x y} → f (x + y) ≡ f x * f y

-- postulate map, flatmap and sum to be homomorphisms
postulate mapBag : (f : ℤ → ℤ) (b : Bag) → Bag
postulate flatmapBag : (f : ℤ → Bag) (b : Bag) → Bag
postulate sumBag : Bag → ℤ
postulate homo-map : ∀ {f} → Homomorphic₂ (mapBag f) _++_ _++_
postulate homo-flatmap : ∀ {f} → Homomorphic₂ (flatmapBag f) _++_ _++_
postulate homo-sum : Homomorphic₂ sumBag _++_ _+_
postulate neg-map : ∀ {f} → Homomorphic₁ (mapBag f) negateBag negateBag
postulate neg-flatmap : ∀ {f} → Homomorphic₁ (flatmapBag f) negateBag negateBag
