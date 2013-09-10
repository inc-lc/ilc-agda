module Atlas.Change.Type where

open import Atlas.Syntax.Type

ΔBase : Base → Base
-- change to a boolean is a xor-rand
ΔBase Bool = Bool
-- change to a map is change to its values
ΔBase (Map key val) = Map key (ΔBase val)

open import Parametric.Change.Type ΔBase public
  using (ΔType)
