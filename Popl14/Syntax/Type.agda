module Popl14.Syntax.Type where

-- Types of Calculus Popl14

data Base : Set where
  base-int : Base
  base-bag : Base

open import Parametric.Syntax.Type Base public

pattern int = base base-int
pattern bag = base base-bag
