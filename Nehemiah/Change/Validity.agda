------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Dependently typed changes with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Validity where

open import Nehemiah.Syntax.Type
open import Nehemiah.Denotation.Value

import Parametric.Change.Validity {Base} ⟦_⟧Base as Validity

open import Nehemiah.Change.Type 
open import Nehemiah.Change.Value

open import Data.Integer
open import Structure.Bag.Nehemiah
open import Base.Change.Algebra as BCA
open import Base.Change.Products
open import Level

{-# TERMINATING #-}
change-algebra-base : ∀ ι → ChangeAlgebra ⟦ ι ⟧Base

instance
  change-algebra-base-family : ChangeAlgebraFamily ⟦_⟧Base
  change-algebra-base-family = family change-algebra-base

open Validity.Structure {{change-algebra-base-family}} public

change-algebra-base base-int = BCA.GroupChanges.changeAlgebraGroup _ {{abelian-int}}
change-algebra-base base-bag = BCA.GroupChanges.changeAlgebraGroup _ {{abelian-bag}}
change-algebra-base (base-pair τ₁ τ₂) = ProductChanges.changeAlgebraProducts {{change-algebra τ₁}} {{change-algebra τ₂}}
