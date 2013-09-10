module Atlas.Syntax.Type where

data Base : Set where
  Bool : Base
  Map : (κ : Base) (ι : Base) → Base

open import Parametric.Syntax.Type Base public
