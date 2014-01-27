module Nehemiah.Change.Validity where

open import Nehemiah.Syntax.Type
open import Nehemiah.Denotation.Value

import Parametric.Change.Validity ⟦_⟧Base as Validity

-- Changes for Calculus Nehemiah

open import Nehemiah.Change.Type 
open import Nehemiah.Change.Value

open import Data.Integer
open import Structure.Bag.Nehemiah
open import Base.Change.Algebra

open import Level

change-algebra-base : ∀ ι → ChangeAlgebra zero ⟦ ι ⟧Base
change-algebra-base base-int = GroupChanges.changeAlgebra ℤ
change-algebra-base base-bag = GroupChanges.changeAlgebra Bag

change-algebra-base-family : ChangeAlgebraFamily zero ⟦_⟧Base
change-algebra-base-family = family change-algebra-base

open Validity.Structure change-algebra-base-family public
