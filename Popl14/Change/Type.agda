module Popl14.Change.Type where

open import Popl14.Syntax.Type

import Parametric.Change.Type Base as ChangeType

ΔBase : ChangeType.Structure
ΔBase base-int = base-int
ΔBase base-bag = base-bag

open ChangeType.Structure ΔBase public
