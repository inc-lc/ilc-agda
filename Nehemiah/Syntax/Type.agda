------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- The syntax of types with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Syntax.Type where

import Parametric.Syntax.Type as Type

data Base : Type.Structure where
  base-int : Base
  base-bag : Base

open Type.Structure Base public

pattern int = base base-int
pattern bag = base base-bag
