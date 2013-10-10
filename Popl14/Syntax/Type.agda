module Popl14.Syntax.Type where

-- Types of Calculus Popl14

import Parametric.Syntax.Type as Type

data Base : Type.Structure where
  base-int : Base
  base-bag : Base

open Type.Structure Base public

pattern int = base base-int
pattern bag = base base-bag
