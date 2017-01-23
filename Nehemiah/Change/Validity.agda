------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Dependently typed changes with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Validity where

open import Nehemiah.Syntax.Type
open import Nehemiah.Denotation.Value

import Parametric.Change.Validity ⟦_⟧Base as Validity

open import Nehemiah.Change.Type 
open import Nehemiah.Change.Value

open import Data.Integer
open import Structure.Bag.Nehemiah
open import Base.Change.Algebra

open import Level

change-algebra-base : ∀ ι → ChangeAlgebra ⟦ ι ⟧Base
change-algebra-base base-int = GroupChanges.changeAlgebra ℤ {{abelian-int}}
change-algebra-base base-bag = GroupChanges.changeAlgebra Bag {{abelian-bag}}

instance
  change-algebra-base-family : ChangeAlgebraFamily ⟦_⟧Base
  change-algebra-base-family = family change-algebra-base

open Validity.Structure {{change-algebra-base-family}} public
