module Structure.Bag.Popl14 where

-- Bags of integers, version Popl14
--
-- This module postulates bags of integers with negative
-- multiplicities as a group under additive union.

open import Relation.Binary.PropositionalEquality
open import Algebra using (CommutativeRing)
open import Algebra.Structures
open import Data.Integer
import Data.Integer.Properties
  renaming (commutativeRing to ℤ-is-commutativeRing)
open Data.Integer.Properties using (ℤ-is-commutativeRing)
open import Data.Product


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

-- postulate Bag as an abelion group
-- [Argue that no inconsistency can be introduced]
postulate Bag : Set
-- singleton
postulate singletonBag : ℤ → Bag
-- union
postulate _++_ : Bag → Bag → Bag
infixr 5 _++_
-- negate = mapMultiplicities (λ z → - z)
postulate negateBag : Bag → Bag
postulate emptyBag : Bag
postulate abelian-bag : IsAbelianGroup _≡_ _++_ emptyBag negateBag

infixl 9 _\\_ -- same as Data.Map.(\\)
_\\_ : Bag → Bag → Bag
d \\ b = d ++ (negateBag b)

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

-- Naming convention follows Algebra.Morphism

-- Homomorphic₁ : morphism preserves negation
Homomorphic₁ :
  {A B : Set} (f : A → B) (negA : A → A) (negB : B → B) → Set
Homomorphic₁ {A} {B} f negA negB = ∀ {x} → f (negA x) ≡ negB (f x)

-- Homomorphic₂ : morphism preserves binary operation.
Homomorphic₂ :
  {A B : Set} (f : A → B) (_+_ : A → A → A) (_*_ : B → B → B) → Set
Homomorphic₂ {A} {B} f _+_ _*_ = ∀ {x y} → f (x + y) ≡ f x * f y

-- postulate map and sum to be (light-weight) homomorphisms
postulate mapBag : (f : ℤ → ℤ) (b : Bag) → Bag
postulate flatmapBag : (f : ℤ → Bag) (b : Bag) → Bag
postulate sumBag : Bag → ℤ
postulate homo-map : ∀ {f} → Homomorphic₂ (mapBag f) _++_ _++_
postulate homo-flatmap : ∀ {f} → Homomorphic₂ (flatmapBag f) _++_ _++_
postulate homo-sum : Homomorphic₂ sumBag _++_ _+_
postulate neg-map : ∀ {f} → Homomorphic₁ (mapBag f) negateBag negateBag
postulate neg-flatmap : ∀ {f} → Homomorphic₁ (flatmapBag f) negateBag negateBag
