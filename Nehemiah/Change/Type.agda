------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Simply-typed changes with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Type where

open import Nehemiah.Syntax.Type

import Parametric.Change.Type Base as ChangeType

ΔBase : ChangeType.Structure
ΔBase base-int = base base-int
ΔBase base-bag = base base-bag

open ChangeType.Structure ΔBase public
