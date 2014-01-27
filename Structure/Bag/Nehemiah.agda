module Structure.Bag.Nehemiah where

-- Bags of integers, version Nehemiah
--
-- This module imports postulates about bags of integers
-- with negative multiplicities as a group under additive union.

open import Postulate.Bag-Nehemiah public

open import Relation.Binary.PropositionalEquality
open import Algebra using (CommutativeRing)
open import Algebra.Structures
open import Data.Integer
import Data.Integer.Properties
  renaming (commutativeRing to ℤ-is-commutativeRing)
open Data.Integer.Properties using (ℤ-is-commutativeRing)
open import Data.Product

infixl 9 _\\_ -- same as Data.Map.(\\)
_\\_ : Bag → Bag → Bag
d \\ b = d ++ (negateBag b)

-- Useful properties of abelian groups
commutative : ∀ {A : Set} {f : A → A → A} {z neg} →
  IsAbelianGroup _≡_ f z neg → (m n : A) → f m n ≡ f n m
commutative = IsAbelianGroup.comm

associative : ∀ {A : Set} {f : A → A → A} {z neg} →
  IsAbelianGroup _≡_ f z neg → (k m n : A) → f (f k m) n ≡ f k (f m n)
associative abelian = IsSemigroup.assoc (IsMonoid.isSemigroup
  (IsGroup.isMonoid (IsAbelianGroup.isGroup abelian)))

left-inverse : ∀ {A : Set} {f : A → A → A} {z neg} →
  IsAbelianGroup _≡_ f z neg → (n : A) → f (neg n) n ≡ z
left-inverse abelian = proj₁
  (IsGroup.inverse (IsAbelianGroup.isGroup abelian))
right-inverse : ∀ {A : Set} {f : A → A → A} {z neg} →
  IsAbelianGroup _≡_ f z neg → (n : A) → f n (neg n) ≡ z
right-inverse abelian = proj₂
  (IsGroup.inverse (IsAbelianGroup.isGroup abelian))

left-identity : ∀ {A : Set} {f : A → A → A} {z neg} →
  IsAbelianGroup _≡_ f z neg → (n : A) → f z n ≡ n
left-identity abelian = proj₁ (IsMonoid.identity
  (IsGroup.isMonoid (IsAbelianGroup.isGroup abelian)))
right-identity : ∀ {A : Set} {f : A → A → A} {z neg} →
  IsAbelianGroup _≡_ f z neg → (n : A) → f n z ≡ n
right-identity abelian = proj₂ (IsMonoid.identity
  (IsGroup.isMonoid (IsAbelianGroup.isGroup abelian)))

abelian-int : IsAbelianGroup _≡_ _+_ (+ 0) -_
abelian-int =
  IsRing.+-isAbelianGroup
  (IsCommutativeRing.isRing
  (CommutativeRing.isCommutativeRing
  ℤ-is-commutativeRing))
commutative-int : (m n : ℤ) → m + n ≡ n + m
commutative-int = commutative abelian-int
associative-int : (k m n : ℤ) → (k + m) + n ≡ k + (m + n)
associative-int = associative abelian-int
right-inv-int : (n : ℤ) → n - n ≡ + 0
right-inv-int = right-inverse abelian-int
left-id-int : (n : ℤ) → (+ 0) + n ≡ n
left-id-int = left-identity abelian-int
right-id-int : (n : ℤ) → n + (+ 0) ≡ n
right-id-int = right-identity abelian-int

commutative-bag : (a b : Bag) → a ++ b ≡ b ++ a
commutative-bag = commutative abelian-bag
associative-bag : (a b c : Bag) → (a ++ b) ++ c ≡ a ++ (b ++ c)
associative-bag = associative abelian-bag
right-inv-bag : (b : Bag) → b \\ b ≡ emptyBag
right-inv-bag = right-inverse abelian-bag
left-id-bag : (b : Bag) → emptyBag ++ b ≡ b
left-id-bag = left-identity abelian-bag
right-id-bag : (b : Bag) → b ++ emptyBag ≡ b
right-id-bag = right-identity abelian-bag
