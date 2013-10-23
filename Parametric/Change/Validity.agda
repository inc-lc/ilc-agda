import Parametric.Syntax.Type as Type
import Parametric.Denotation.Value as Value

module Parametric.Change.Validity
    {Base : Type.Structure}
    (⟦_⟧Base : Value.Structure Base)
  where

open Type.Structure Base
open Value.Structure Base ⟦_⟧Base

open import Base.Denotation.Notation public

open import Relation.Binary.PropositionalEquality
open import Base.Change.Algebra as CA
  using (ChangeAlgebraFamily)
open import Level

Structure : Set₁
Structure = ChangeAlgebraFamily zero ⟦_⟧Base

module Structure (change-algebra-base : Structure) where
  -- change algebras

  open CA public renaming
    ( [] to ∅
    ; _∷_ to _•_
    )

  -- change algebra for every type

  change-algebra : ∀ τ → ChangeAlgebra zero ⟦ τ ⟧Type
  change-algebra (base ι) = change-algebra₍ ι ₎
  change-algebra (τ₁ ⇒ τ₂) = CA.FunctionChanges.changeAlgebra _ _ {{change-algebra τ₁}} {{change-algebra τ₂}}

  change-algebra-family : ChangeAlgebraFamily zero ⟦_⟧Type
  change-algebra-family = family change-algebra

  -- function changes

  open FunctionChanges public using (cons)
  module _ {τ₁ τ₂ : Type} where
    open FunctionChanges.FunctionChange _ _ {{change-algebra τ₁}} {{change-algebra τ₂}} public
      renaming
        ( correct to is-valid
        ; apply to call-change
        )

  -- environment changes

  open ListChanges ⟦_⟧Type {{change-algebra-family}} public using () renaming
    ( changeAlgebra to environment-changes
    )

  after-env : ∀ {Γ : Context} → {ρ : ⟦ Γ ⟧} (dρ : Δ₍  Γ ₎ ρ) → ⟦ Γ ⟧
  after-env {Γ} = after₍ Γ ₎
