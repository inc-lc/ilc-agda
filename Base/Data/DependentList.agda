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

IndependentList : ∀ {a} →
  (A : Set a) {irrelevant : List.List ⊤} → Set a
IndependentList A {irrelevant} = DependentList (λ _ → A) irrelevant

from-list : ∀ {x} {X : Set x} →
  (list : List X) → IndependentList X {List.map (λ _ → tt) list}
from-list [] = ∅
from-list (x ∷ xs) = x • (from-list xs)

to-list : ∀ {a b} {A : Set a} {F : A → Set b}
  {list : List A} → DependentList F list → List (Σ A F)
to-list ∅ = []
to-list (_•_ {type-head} head tail) = (type-head , head) ∷ to-list tail

{-
-- fully dependent map; useless for now
map : ∀ {a b c d}
  {A : Set a} {B : Set b} {F : A → Set c} {G : Σ A F → Set d}
  {dummy-list} →
  (f : {x : A} → (y : F x) → G (x , y)) →
  (input : DependentList F dummy-list) →
  DependentList G (to-list input)

map {F = F} {G} f = loop where
  loop : ∀ {dummy-list}
    (input : DependentList F dummy-list) →
    DependentList G (to-list input)
  loop ∅ = ∅
  loop (head • tail) = f head • loop tail
-}

-- Ignore input Values in the output Type
-- CAUTION: confuses termination checker if used in inductive proofs
map-IVT : ∀ {a b c : Level}
  {A : Set a} {F : A → Set b} {G : A → Set c}
  {type-args : List A}
  (f : {x : A} → F x → G x) →
  DependentList F type-args → DependentList G type-args

map-IVT {F = F} {G} f = loop where
  loop : ∀ {type-args} →
    DependentList F type-args → DependentList G type-args
  loop ∅ = ∅
  loop (head • tail) = f head • loop tail
