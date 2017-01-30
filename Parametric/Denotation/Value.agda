------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Values for standard evaluation (Def. 3.1 and 3.2, Fig. 4c and 4f).
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type

module Parametric.Denotation.Value
    (Base : Type.Structure)
  where

open import Base.Denotation.Notation

open Type.Structure Base

-- Extension point: Values for base types.
Structure : Set₁
Structure = Base Type → Set

module Structure (⟦_⟧Base : Structure) where
  -- We provide: Values for arbitrary types.
  ⟦_⟧Type : Type → Set
  ⟦ base ι ⟧Type = ⟦ ι ⟧Base
  ⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

  instance
    -- This means: Overload ⟦_⟧ to mean ⟦_⟧Type.
    meaningOfType : Meaning Type
    meaningOfType = meaning ⟦_⟧Type

  -- We also provide: Environments of such values.
  open import Base.Denotation.Environment Type ⟦_⟧Type public
