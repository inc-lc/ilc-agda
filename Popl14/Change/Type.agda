module Popl14.Change.Type where

open import Popl14.Syntax.Type

Popl14-Δbase : Base → Base
Popl14-Δbase base-int = base-int
Popl14-Δbase base-bag = base-bag

open import Parametric.Change.Type Popl14-Δbase public
