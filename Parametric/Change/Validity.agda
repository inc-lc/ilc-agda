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

open import Base.Change.Algebra as CA using
  ( ChangeAlgebra
  ; ChangeAlgebraFamily
  ; change-algebra₍_₎
  ; family
  )
open import Level

Structure : Set₁
Structure = ChangeAlgebraFamily zero ⟦_⟧Base

module Structure (change-algebra-base : Structure) where
  change-algebra : ∀ τ → ChangeAlgebra zero ⟦ τ ⟧Type
  change-algebra (base ι) = change-algebra₍ ι ₎
  change-algebra (τ₁ ⇒ τ₂) = CA.FunctionChanges.changeAlgebra _ _ {{change-algebra τ₁}} {{change-algebra τ₂}}

  change-algebra-family : ChangeAlgebraFamily zero ⟦_⟧Type
  change-algebra-family = family change-algebra

  ----------------
  -- Parameters --
  ----------------

  Change-base : (ι : Base) → ⟦ ι ⟧Base → Set
  Change-base = CA.Δ₍_₎

  diff-change-base : ∀ ι → (u v : ⟦ ι ⟧Base) → Change-base ι v
  diff-change-base = CA.diff′

  ---------------
  -- Interface --
  ---------------

  open CA public
    using
      ( Δ₍_₎
      )
    renaming
      ( update′ to apply-change
      ; diff′ to diff-change
      ; nil₍_₎ to nil-change
      )

  -- Lemma apply-diff
  v+[u-v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} →
    v ⊞₍ τ ₎ (u ⊟₍ τ ₎ v) ≡ u
  v+[u-v]=u {τ} {u} {v} = CA.update-diff₍ τ ₎ u v

  --------------------
  -- Implementation --
  --------------------

  module _ {τ₁ τ₂ : Type} where
    open CA.FunctionChanges.FunctionChange _ _ {{change-algebra τ₁}} {{change-algebra τ₂}} public
      using
        (
        )
      renaming
        ( correct to is-valid
        ; apply to call-change
        )

  open CA public using
    ( before
    ; after
    ; before₍_₎
    ; after₍_₎
    )

  ------------------
  -- Environments --
  ------------------

  open CA.FunctionChanges public using (cons)
  open CA public using () renaming
    ( [] to ∅
    ; _∷_ to _•_
    )

  open CA.ListChanges ⟦_⟧Type {{change-algebra-family}} public using () renaming
    ( changeAlgebra to environment-changes
    )

  after-env : ∀ {Γ : Context} → {ρ : ⟦ Γ ⟧} (dρ : Δ₍  Γ ₎ ρ) → ⟦ Γ ⟧
  after-env {Γ} = after₍ Γ ₎
