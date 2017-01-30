------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Simply-typed changes with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Type where

open import Nehemiah.Syntax.Type

import Parametric.Change.Type Base as ChangeType

{-# TERMINATING #-}
ΔBase : ChangeType.Structure

open ChangeType.Structure ΔBase public

ΔBase base-int = base base-int
ΔBase base-bag = base base-bag
ΔBase (base-pair τ₁ τ₂) = ΔType τ₁ pair ΔType τ₂
