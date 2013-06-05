-- An agda type isomorphic to bags of natural numbers

-- How to import this file from anywhere in the world
--
-- 1. M-x customize-group RET agda2 RET
-- 2. Look for the option `Agda2 Include Dirs`
-- 3. Insert "$ILC/agda", where $ILC is path to ILC repo on your computer
-- 4. "Save for future sessions"
-- 5. open import Data.NatBag

module Data.NatBag where

open import Data.Nat hiding (zero) renaming (_+_ to plus)
open import Data.Integer renaming (suc to +1 ; pred to -1)
open import Data.Sum hiding (map)
open import Relation.Binary.PropositionalEquality

-----------
-- Types --
-----------

IsZero : ℤ → Set
IsZero i = i ≡ + 0

data Nonzero : ℤ → Set where
  negative : (n : ℕ) → Nonzero -[1+ n ]
  positive : (n : ℕ) → Nonzero (+ (suc n))

data EmptyBag : Set where
  ∅ : EmptyBag

data NonemptyBag : Set where
  singleton : (i : ℤ) → (i≠0 : Nonzero i) → NonemptyBag
  _∷_ : (i : ℤ) → (bag : NonemptyBag) → NonemptyBag

infixr 5 _∷_

Bag : Set
Bag = EmptyBag ⊎ NonemptyBag

-------------------
-- Bag interface --
-------------------

empty : Bag

insert : ℕ → Bag → Bag

delete : ℕ → Bag → Bag

lookup : ℕ → Bag → ℤ

update : ℕ → ℤ → Bag → Bag

updateWith : ℕ → (ℤ → ℤ) → Bag → Bag

map : (ℕ → ℕ) → Bag → Bag -- map on bags, mapKeys on maps

map₂ : (ℤ → ℤ) → Bag → Bag -- mapValues on maps

zipWith : (ℤ → ℤ → ℤ) → Bag → Bag → Bag

_++_ : Bag → Bag → Bag
infixr 5 _++_ -- right-associativity follows Haskell, for efficiency

_\\_ : Bag → Bag → Bag
infixl 9 _\\_ -- fixity follows Haskell's Data.Map.(\\)

--------------------
-- Implementation --
--------------------

insert n bag = updateWith n +1 bag

delete n bag = updateWith n -1 bag

update n i bag = updateWith n (λ _ → i) bag

_++_ = zipWith _+_

_\\_ = zipWith _-_

zero : ℤ
zero = + 0

-- It is very easy to compute a proof that an integer is
-- nonzero whenever such a thing exists.
nonzero? : (i : ℤ) → IsZero i ⊎ Nonzero i
nonzero? (+ 0) = inj₁ refl
nonzero? (+ (suc n)) = inj₂ (positive n)
nonzero? -[1+ n ] = inj₂ (negative n)

empty = inj₁ ∅

makeSingleton : ℕ → (i : ℤ) → Nonzero i → NonemptyBag
makeSingleton 0 i i≠0 = singleton i i≠0
makeSingleton (suc n) i i≠0 = (+ 0) ∷ makeSingleton n i i≠0

updateWith n f (inj₁ ∅) with nonzero? (f zero)
... | inj₁ _ = empty
... | inj₂ i≠0 = inj₂ (makeSingleton n (f zero) i≠0)
updateWith 0 f (inj₂ (singleton i i≠0)) with nonzero? (f i)
... | inj₁ _ = empty
... | inj₂ j≠0 = inj₂ (singleton (f i) j≠0)
updateWith (suc n) f (inj₂ (singleton i i≠0)) with nonzero? (f zero)
... | inj₁ _ = inj₂ (singleton i i≠0)
... | inj₂ j≠0 = inj₂ (i ∷ makeSingleton n (f zero) j≠0)
updateWith 0 f (inj₂ (i ∷ bag)) = inj₂ (f i ∷ bag)
updateWith (suc n) f (inj₂ (i ∷ y))
  with updateWith n f (inj₂ y) | nonzero? i
... | inj₁ ∅ | inj₁ _ = empty
... | inj₁ ∅ | inj₂ i≠0 = inj₂ (singleton i i≠0)
... | inj₂ bag | _ = inj₂ (i ∷ bag)

lookupNonempty : ℕ → NonemptyBag → ℤ
lookupNonempty 0 (singleton i i≠0) = i
lookupNonempty (suc n) (singleton i i≠0) = zero
lookupNonempty 0 (i ∷ bag) = i
lookupNonempty (suc n) (i ∷ bag) = lookupNonempty n bag

lookup n (inj₁ ∅) = zero
lookup n (inj₂ bag) = lookupNonempty n bag

-- It is possible to get empty bags by mapping over a nonempty bag:
-- map (λ _ → 3) { 1 ⇒ 5 , 2 ⇒ -5 }
mapKeysFrom : ℕ → (ℕ → ℕ) → NonemptyBag → Bag
mapKeysFrom n f (singleton i i≠0) = inj₂ (makeSingleton (f n) i i≠0)
mapKeysFrom n f (i ∷ bag) with nonzero? i
... | inj₁ _ = mapKeysFrom (suc n) f bag
... | inj₂ i≠0 = updateWith (f n) (λ j → j + i) (mapKeysFrom (suc n) f bag)

map f (inj₁ ∅) = empty
map f (inj₂ bag) = mapKeysFrom 0 f bag

mapNonempty₂ : (ℤ → ℤ) → NonemptyBag → Bag
mapNonempty₂ f (singleton i i≠0) with nonzero? (f i)
... | inj₁ _ = empty
... | inj₂ j≠0 = inj₂ (singleton (f i) j≠0)
mapNonempty₂ f (i ∷ bag₀)
  with mapNonempty₂ f bag₀ | nonzero? (f i)
... | inj₁ ∅   | inj₁ _  = empty
... | inj₁ ∅   | inj₂ j≠0 = inj₂ (singleton (f i) j≠0)
... | inj₂ bag | _        = inj₂ (f i ∷ bag)

map₂ f (inj₁ ∅) = empty
map₂ f (inj₂ b) = mapNonempty₂ f b

zipLeft : (ℤ → ℤ → ℤ) → NonemptyBag → Bag
zipLeft f b₁ = mapNonempty₂ (λ x → f x zero) b₁

zipRight : (ℤ → ℤ → ℤ) → NonemptyBag → Bag
zipRight f b₂ = mapNonempty₂ (λ y → f zero y) b₂

zipNonempty : (ℤ → ℤ → ℤ) → NonemptyBag → NonemptyBag → Bag
zipNonempty f (singleton i i≠0) (singleton j j≠0) with nonzero? (f i j)
... | inj₁ _ = empty
... | inj₂ k≠0 = inj₂ (singleton (f i j) k≠0)
zipNonempty f (singleton i i≠0) (j ∷ b₂)
  with zipRight f b₂ | nonzero? (f i j)
... | inj₁ ∅ | inj₁ _ = empty
... | inj₁ ∅ | inj₂ k≠0 = inj₂ (singleton (f i j) k≠0)
... | inj₂ bag | _ = inj₂ (f i j ∷ bag)
zipNonempty f (i ∷ b₁) (singleton j j≠0)
  with zipLeft f b₁ | nonzero? (f i j)
... | inj₁ ∅ | inj₁ _ = empty
... | inj₁ ∅ | inj₂ k≠0 = inj₂ (singleton (f i j) k≠0)
... | inj₂ bag | _ = inj₂ (f i j ∷ bag)
zipNonempty f (i ∷ b₁) (j ∷ b₂)
  with zipNonempty f b₁ b₂ | nonzero? (f i j)
... | inj₁ ∅ | inj₁ _ = empty
... | inj₁ ∅ | inj₂ k≠0 = inj₂ (singleton (f i j) k≠0)
... | inj₂ bag | _ = inj₂ (f i j ∷ bag)

zipWith f (inj₁ ∅) (inj₁ ∅) = empty
zipWith f (inj₁ ∅) (inj₂ b₂) = zipRight f b₂
zipWith f (inj₂ b₁) (inj₁ ∅) = zipLeft f b₁
zipWith f (inj₂ b₁) (inj₂ b₂) = zipNonempty f b₁ b₂
