module Sorting where

import Level as L

open import Data.Empty
open import Data.List
open import Data.Sum
open import Function
open import Relation.Binary
open import Relation.Nullary

-- Here I mostly follow the insertion sort developed in:
-- http://mazzo.li/posts/AgdaSort.html
--
-- The main difference, apart from a few identifiers, is that I use the standard
-- library.

module Sort {c ℓ₁ ℓ₂}  {X : Set c}
                       {_≈_ : Rel X ℓ₁} {_≤_ : Rel X ℓ₂}
                       (ord : IsDecTotalOrder _≈_ _≤_)
                       where
  open IsDecTotalOrder ord

  data ⊥X⊤ : Set c where
    ⟦⊥⟧ ⟦⊤⟧ : ⊥X⊤
    ⟦_⟧ : X → ⊥X⊤

  data _≲_ : Rel ⊥X⊤ (c L.⊔ ℓ₂) where
    ⊥≲_ : ∀ {x} → ⟦⊥⟧ ≲ x
    _≲⊤ : ∀ {x} → x ≲ ⟦⊤⟧
    ≤-lift : ∀ {x y} → x ≤ y → ⟦ x ⟧ ≲ ⟦ y ⟧

  data OList (l u : ⊥X⊤) : Set (c L.⊔ ℓ₂) where
    nil : l ≲ u → OList l u
    cons : ∀ x (xs : OList ⟦ x ⟧ u) → l ≲ ⟦ x ⟧ → OList l u

  toList : ∀ {l u} → OList l u → List X
  toList (nil _) = []
  toList (cons x xs _) = x ∷ toList xs

  insert : ∀ {l u} y → OList l u → l ≲ ⟦ y ⟧ → ⟦ y ⟧ ≲ u → OList l u
  insert y (nil _) l≲y y≲u = cons y (nil y≲u) l≲y
  insert y (cons x xs l≲x) l≲y y≲u with y ≤? x
  insert y (cons x xs l≲x) l≲y y≲u | yes p = cons y (cons x xs (≤-lift p)) l≲y
  insert y (cons x xs l≲x) l≲y y≲u | no y>x = cons x (insert y xs x≲y y≲u) l≲x
    where
      x≲y : ⟦ x ⟧ ≲ ⟦ y ⟧
      -- Ambiguous
      --x≲y = [ ≤-lift , ⊥-elim ∘ y>x ] (total x y)
      --x≲y = (λ r → [ ≤-lift , ⊥-elim ∘ y>x ] r) (total x y)

      -- This is instead not ambiguous, somehow.
      x≲y with total x y 
      ... | r = [ ≤-lift , ⊥-elim ∘ y>x ] r

  UList = OList ⟦⊥⟧ ⟦⊤⟧
  unil : UList
  unil = nil ⊥≲_

  ucons : X → UList → UList
  ucons x xs = insert x xs ⊥≲_ _≲⊤

  uunion-asym : UList → List X → UList
  uunion-asym = foldr (λ x xs → insert {⟦⊥⟧} {⟦⊤⟧} x xs ⊥≲_ _≲⊤)

  uunion : UList → UList → UList
  uunion b₁ b₂ = uunion-asym b₁ (toList b₂)

  uToList : UList → List X
  uToList = toList

  isort′ : List X → UList
  isort′ = uunion-asym (nil ⊥≲_)

  isort = toList ∘ isort′

--open Sort using (isort) public
