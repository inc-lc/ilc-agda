------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Simply-typed changes (Fig. 3 and Fig. 4d)
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type

module Parametric.Change.Type
  (Base : Type.Structure)
  where

open Type.Structure Base

-- Extension point: Simply-typed changes of base types.
Structure : Set
Structure = Base → Base

module Structure (ΔBase : Structure) where
  -- We provide: Simply-typed changes on simple types.
  ΔType : Type → Type
  ΔType (base ι) = base (ΔBase ι)
  ΔType (σ ⇒ τ) = σ ⇒ ΔType σ ⇒ ΔType τ

  -- And we also provide context merging.
  open import Base.Change.Context ΔType public
