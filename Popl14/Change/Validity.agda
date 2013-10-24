module Popl14.Change.Validity where

open import Popl14.Syntax.Type
open import Popl14.Denotation.Value

import Parametric.Change.Validity ⟦_⟧Base as Validity

-- Changes for Calculus Popl14

open import Popl14.Change.Type 
open import Popl14.Change.Value

open import Data.Integer
open import Structure.Bag.Popl14
open import Base.Change.Algebra

open import Level

change-algebra-base : ∀ ι → ChangeAlgebra zero ⟦ ι ⟧Base
change-algebra-base base-int = GroupChanges.changeAlgebra ℤ
change-algebra-base base-bag = GroupChanges.changeAlgebra Bag

change-algebra-base-family : ChangeAlgebraFamily zero ⟦_⟧Base
change-algebra-base-family = family change-algebra-base

open Validity.Structure change-algebra-base-family public
