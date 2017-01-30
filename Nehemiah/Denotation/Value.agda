------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Values for standard evaluation with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Denotation.Value where

open import Nehemiah.Syntax.Type public
open import Nehemiah.Change.Type public
open import Base.Denotation.Notation public

open import Structure.Bag.Nehemiah
open import Data.Product
open import Data.Integer

import Parametric.Denotation.Value Base as Value

{-# TERMINATING #-}
⟦_⟧Base : Value.Structure

open Value.Structure ⟦_⟧Base public

⟦ base-int ⟧Base = ℤ
⟦ base-bag ⟧Base = Bag
⟦ base-pair τ₁ τ₂ ⟧Base = ⟦ τ₁ ⟧Type × ⟦ τ₂ ⟧Type
