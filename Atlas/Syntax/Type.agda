module Atlas.Syntax.Type where

import Parametric.Syntax.Type as Type

data Base : Type.Structure where
  Bool : Base
  Map : (κ : Base) (ι : Base) → Base

open Type.Structure Base public
