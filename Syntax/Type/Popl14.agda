module Syntax.Type.Popl14 where

-- Types of Calculus Popl14

data Popl14-type : Set where
  base-int : Popl14-type
  base-bag : Popl14-type

open import Syntax.Type.Plotkin Popl14-type public

pattern int = base base-int
pattern bag = base base-bag

Popl14-Δbase : Popl14-type → Popl14-type
Popl14-Δbase base-int = base-int
Popl14-Δbase base-bag = base-bag

ΔType : Type → Type
ΔType = lift-Δtype₀ Popl14-Δbase
