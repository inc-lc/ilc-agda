module Atlas.Syntax.Type where

data Base : Set where
  Bool : Base
  Map : (κ : Base) (ι : Base) → Base

open import Parametric.Syntax.Type Base public

ΔBase : Base → Base
-- change to a boolean is a xor-rand
ΔBase Bool = Bool
-- change to a map is change to its values
ΔBase (Map key val) = Map key (ΔBase val)

open import Parametric.Change.Type ΔBase public
  using (ΔType)
