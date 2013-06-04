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
open import Data.Maybe.Core
open import Data.Sum

-----------
-- Types --
-----------

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

map₁ : (ℕ → ℕ) → Bag → Bag -- map on bags, mapKeys on maps

map₂ : (ℤ → ℤ) → Bag → Bag -- mapValues on maps

{- TODO: Wait for map.
zipWith : (ℤ → ℤ → ℤ) → Bag → Bag → Bag

_++_ : Bag → Bag → Bag
infixr 5 _++_ -- right-associativity follows Haskell, for efficiency

_\\_ : Bag → Bag → Bag
infixl 9 _\\_ -- fixity follows Haskell's Data.Map.(\\)
-}

--------------------
-- Implementation --
--------------------

insert n bag = updateWith n +1 bag

delete n bag = updateWith n -1 bag

update n i bag = updateWith n (λ _ → i) bag

zero : ℤ
zero = + 0

-- It is very easy to compute a proof that an integer is
-- nonzero whenever such a thing exists.
nonzero? : (i : ℤ) → Maybe (Nonzero i)
nonzero? (+ 0) = nothing
nonzero? (+ (suc n)) = just (positive n)
nonzero? -[1+ n ] = just (negative n)

empty = inj₁ ∅

makeSingleton : ℕ → (i : ℤ) → Nonzero i → NonemptyBag
makeSingleton 0 i i≠0 = singleton i i≠0
makeSingleton (suc n) i i≠0 = (+ 0) ∷ makeSingleton n i i≠0

updateWith n f (inj₁ ∅) with nonzero? (f zero)
... | nothing = empty
... | just i≠0 = inj₂ (makeSingleton n (f zero) i≠0)
updateWith 0 f (inj₂ (singleton i i≠0)) with nonzero? (f i)
... | nothing = empty
... | just j≠0 = inj₂ (singleton (f i) j≠0)
updateWith (suc n) f (inj₂ (singleton i i≠0)) with nonzero? (f zero)
... | nothing = inj₂ (singleton i i≠0)
... | just j≠0 = inj₂ (i ∷ makeSingleton n (f zero) j≠0)
updateWith 0 f (inj₂ (i ∷ bag)) = inj₂ (f i ∷ bag)
updateWith (suc n) f (inj₂ (i ∷ y))
  with updateWith n f (inj₂ y) | nonzero? i
... | inj₁ ∅ | nothing = empty
... | inj₁ ∅ | just i≠0 = inj₂ (singleton i i≠0)
... | inj₂ bag | _ = inj₂ (i ∷ bag)

lookupNonempty : ℕ → NonemptyBag → ℤ
lookupNonempty 0 (singleton i i≠0) = i
lookupNonempty (suc n) (singleton i i≠0) = zero
lookupNonempty 0 (i ∷ bag) = i
lookupNonempty (suc n) (i ∷ bag) = lookupNonempty n bag

lookup n (inj₁ ∅) = zero
lookup n (inj₂ bag) = lookupNonempty n bag

-- It is possible to get empty bags by mapping over a nonempty bag:
-- map₁ (λ _ → 3) { 1 ⇒ 5 , 2 ⇒ -5 }
mapKeysFrom : ℕ → (ℕ → ℕ) → NonemptyBag → Bag
mapKeysFrom n f (singleton i i≠0) = inj₂ (makeSingleton (f n) i i≠0)
mapKeysFrom n f (i ∷ bag) with nonzero? i
... | nothing = mapKeysFrom (suc n) f bag
... | just i≠0 = updateWith (f n) (λ j → j + i) (mapKeysFrom (suc n) f bag)

map₁ f (inj₁ ∅) = empty
map₁ f (inj₂ bag) = mapKeysFrom 0 f bag

map₂ f (inj₁ ∅) = empty
map₂ f (inj₂ (singleton i i≠0)) = {!!}
map₂ f (inj₂ (i ∷ bag₀)) with map₂ f (inj₂ bag₀) | nonzero? i | nonzero? (f i)
-- If an element has multiplicity 0, it should not be mapped over.
-- Conceptually, we are mapping over the values of this infinite
-- map not by f, but by {case 0 => 0}.orElse(f).
... | inj₁ ∅   | nothing  | _        = empty
... | inj₂ bag | nothing  | _        = inj₂ (zero ∷ bag)
... | inj₁ ∅   | just i≠0 | nothing  = empty
... | inj₁ ∅   | just i≠0 | just j≠0 = inj₂ (singleton (f i) j≠0)
... | inj₂ bag | just i≠0 | _        = inj₂ (f i ∷ bag)

{- TODO: Redefine in terms of zipWith, which will be defined
         in terms of map.
-- The union of nonempty bags (with possibly negative
-- multiplicities) can be empty.
unionNonempty : NonemptyBag → NonemptyBag → Bag
unionNonempty (singleton i i≠0) (singleton j j≠0) with nonzero? (i + j)
... | nothing = empty
... | just k≠0 = inj₂ (singleton (i + j) k≠0)
unionNonempty (singleton i i≠0) (j ∷ b₂) = inj₂ (i + j ∷ b₂)

inj₁ ∅ ++ b₂ = b₂
b₁ ++ inj₁ ∅ = b₁
(inj₂ b₁) ++ (inj₂ b₂) = (unionNonempty b₁ b₂)
-}
