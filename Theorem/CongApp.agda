module Theorem.CongApp where

-- Theorem CongApp.
-- If f ≡ g and x ≡ y, then (f x) ≡ (g y).

open import Relation.Binary.PropositionalEquality public

infixl 0 _⟨$⟩_

_⟨$⟩_ : ∀ {a b} {A : Set a} {B : Set b}
  {f g : A → B} {x y : A} →
  f ≡ g → x ≡ y → f x ≡ g y

_⟨$⟩_ = cong₂ (λ x y → x y)
