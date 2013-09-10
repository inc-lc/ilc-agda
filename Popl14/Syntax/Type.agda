module Popl14.Syntax.Type where

-- Types of Calculus Popl14

data Popl14-type : Set where
  base-int : Popl14-type
  base-bag : Popl14-type

open import Parametric.Syntax.Type Popl14-type public

pattern int = base base-int
pattern bag = base base-bag

Popl14-Δbase : Popl14-type → Popl14-type
Popl14-Δbase base-int = base-int
Popl14-Δbase base-bag = base-bag

open import Parametric.Change.Type Popl14-Δbase public
