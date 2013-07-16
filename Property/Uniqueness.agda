module Property.Uniqueness where

-- A set is unique if it has at most one member.
open import Relation.Binary.PropositionalEquality

uniq : Set → Set
uniq A = ∀ {x y : A} → x ≡ y
