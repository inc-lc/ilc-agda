module Popl14.Syntax.Term where

open import Popl14.Syntax.Type

open import Data.Integer

import Parametric.Syntax.Term Base as Term

-- Popl14-Const ? No.
data Const : Term.Structure where
  intlit-c : (n : ℤ) → Const ∅ int
  add-c : Const (int • int • ∅) int
  minus-c : Const (int • ∅) (int)

  empty-c : Const ∅ (bag)
  insert-c : Const (int • bag • ∅) (bag)
  union-c : Const (bag • bag • ∅) (bag)
  negate-c : Const (bag • ∅) (bag)

  flatmap-c : Const ((int ⇒ bag) • bag • ∅) (bag)
  sum-c : Const (bag • ∅) (int)

open Term.Structure Const public

-- Shorthands of constants

pattern intlit n = const (intlit-c n) ∅
pattern add s t = const add-c (s • t • ∅)
pattern minus t = const minus-c (t • ∅)
pattern empty = const empty-c ∅
pattern insert s t = const insert-c (s • t • ∅)
pattern union s t = const union-c (s • t • ∅)
pattern negate t = const negate-c (t • ∅)
pattern flatmap s t = const flatmap-c (s • t • ∅)
pattern sum t = const sum-c (t • ∅)
