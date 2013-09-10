module Atlas.Syntax.Type where

data Base : Set where
  Bool : Base
  Map : (κ : Base) (ι : Base) → Base

open import Parametric.Syntax.Type Base public

Atlas-Δbase : Base → Base
-- change to a boolean is a xor-rand
Atlas-Δbase Bool = Bool
-- change to a map is change to its values
Atlas-Δbase (Map key val) = Map key (Atlas-Δbase val)

open import Parametric.Change.Type Atlas-Δbase

Atlas-Δtype : Type → Type
Atlas-Δtype = ΔType

