------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Dependently typed changes (Def 3.4 and 3.5, Fig. 4b and 4e)
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Denotation.Value as Value
open import Base.Change.Algebra as CA
  using (ChangeAlgebraFamily)

module Parametric.Change.Validity
    {Base : Type.Structure}
    (⟦_⟧Base : Value.Structure Base)
  where

open Type.Structure Base
open Value.Structure Base ⟦_⟧Base

open import Base.Denotation.Notation public

open import Relation.Binary.PropositionalEquality
open import Level

-- Extension Point: Change algebras for base types
Structure : Set₁
Structure = ChangeAlgebraFamily ⟦_⟧Base

module Structure {{change-algebra-base : Structure}} where
  -- change algebras

  open CA public renaming
    -- Constructors for All′
    ( [] to ∅
    ; _∷_ to _•_
    )

  -- We provide: change algebra for every type
  instance
    change-algebra : ∀ τ → ChangeAlgebra ⟦ τ ⟧Type
    change-algebra (base ι) = change-algebra₍ ι ₎
    change-algebra (τ₁ ⇒ τ₂) = changeAlgebraFun {{change-algebra τ₁}} {{change-algebra τ₂}}

    change-algebra-family : ChangeAlgebraFamily ⟦_⟧Type
    change-algebra-family = family change-algebra

  -- function changes

  module _ {τ₁ τ₂ : Type} where
    open FunctionChange {{change-algebra τ₁}} {{change-algebra τ₂}} public
      renaming
        ( correct to is-valid
        ; apply to call-change
        )

  -- We also provide: change environments (aka. environment changes).

  open ListChanges ⟦_⟧Type {{change-algebra-family}} public using () renaming
    ( changeAlgebraListChanges to environment-changes
    )

  after-env : ∀ {Γ : Context} → {ρ : ⟦ Γ ⟧} (dρ : Δ₍ Γ ₎ ρ) → ⟦ Γ ⟧
  after-env {Γ} = after₍_₎ Γ
