------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- The syntax of terms with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Syntax.Term where

open import Nehemiah.Syntax.Type

open import Data.Integer

import Parametric.Syntax.Term Base as Term

data Const : Term.Structure where
  intlit-const : (n : ℤ) → Const ∅ int
  add-const : Const (int • int • ∅) int
  minus-const : Const (int • ∅) (int)

  empty-const : Const ∅ (bag)
  insert-const : Const (int • bag • ∅) (bag)
  union-const : Const (bag • bag • ∅) (bag)
  negate-const : Const (bag • ∅) (bag)

  flatmap-const : Const ((int ⇒ bag) • bag • ∅) (bag)
  sum-const : Const (bag • ∅) (int)

open Term.Structure Const public

-- Shorthands of constants

pattern intlit n = const (intlit-const n) ∅
pattern add s t = const add-const (s • t • ∅)
pattern minus t = const minus-const (t • ∅)
pattern empty = const empty-const ∅
pattern insert s t = const insert-const (s • t • ∅)
pattern union s t = const union-const (s • t • ∅)
pattern negate t = const negate-const (t • ∅)
pattern flatmap s t = const flatmap-const (s • t • ∅)
pattern sum t = const sum-const (t • ∅)
