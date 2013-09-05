module Syntax.Type.Atlas where

data Atlas-type : Set where
  Bool : Atlas-type
  Map : (κ : Atlas-type) (ι : Atlas-type) → Atlas-type

open import Syntax.Type.Plotkin Atlas-type public

Atlas-Δbase : Atlas-type → Atlas-type
-- change to a boolean is a xor-rand
Atlas-Δbase Bool = Bool
-- change to a map is change to its values
Atlas-Δbase (Map key val) = Map key (Atlas-Δbase val)

open import Syntax.DeltaType Atlas-Δbase

Atlas-Δtype : Type → Type
Atlas-Δtype = ΔType

