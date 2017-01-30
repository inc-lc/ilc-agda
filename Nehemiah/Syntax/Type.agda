------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- The syntax of types with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Syntax.Type where

import Parametric.Syntax.Type as Type

module _ (Type : Set) where
  data Base : Set where
    base-int : Base
    base-bag : Base
    base-pair : (τ₁ : Type) → (τ₂ : Type) → Base

open Type.Structure Base public

pattern int = base base-int
pattern bag = base base-bag
pattern _pair_ a b = base (base-pair a b)
