module Nehemiah.Change.Type where

open import Nehemiah.Syntax.Type

import Parametric.Change.Type Base as ChangeType

ΔBase : ChangeType.Structure
ΔBase base-int = base-int
ΔBase base-bag = base-bag

open ChangeType.Structure ΔBase public
