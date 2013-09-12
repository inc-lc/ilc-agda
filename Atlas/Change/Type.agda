module Atlas.Change.Type where

open import Atlas.Syntax.Type

import Parametric.Change.Type Base as ChangeType

ΔBase : ChangeType.Structure
-- change to a boolean is a xor-rand
ΔBase Bool = Bool
-- change to a map is change to its values
ΔBase (Map key val) = Map key (ΔBase val)

open ChangeType.Structure ΔBase public
