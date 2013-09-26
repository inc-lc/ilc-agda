module Base.Data.DependentList where

open import Level

open import Data.Unit
open import Data.Product using (Σ ; _×_ ; _,_)

import Data.List as List
open List using (List ; [] ; _∷_)

data DependentList {a b} {A : Set a}
  (F : A → Set b) : (type-args : List A) → Set (a ⊔ b)
  where
  ∅ : DependentList F []
  _•_ : ∀ {type-arg} {other-type-args}
    (head : F type-arg)
    (tail : DependentList F other-type-args) →
    DependentList F (type-arg ∷ other-type-args)

infixr 5 _•_
