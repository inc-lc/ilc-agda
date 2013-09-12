module Popl14.Change.Type where

open import Popl14.Syntax.Type

ΔBase : Base → Base
ΔBase base-int = base-int
ΔBase base-bag = base-bag

open import Parametric.Change.Type ΔBase public
