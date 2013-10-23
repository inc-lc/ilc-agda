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
      (
      )
    renaming
      ( Δ₍_₎ to Change
      ; update′ to apply-change
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

  -- abbrevitations
  before₍_₎ : ∀ τ {v} → Change τ v → ⟦ τ ⟧Type
  before₍ τ ₎ {v} _ = v

  after₍_₎ : ∀ τ {v} → Change τ v → ⟦ τ ⟧Type
  after₍ τ ₎ {v} dv = v ⊞₍ τ ₎ dv

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

  ΔEnv : ∀ (Γ : Context) → ⟦ Γ ⟧ → Set
  ΔEnv Γ ρ = CA.Δ₍ Γ ₎ ρ

  ignore : ∀ {Γ : Context} → {ρ : ⟦ Γ ⟧} (dρ : ΔEnv Γ ρ) → ⟦ Γ ⟧
  ignore {Γ} {ρ} _ = ρ

  update : ∀ {Γ : Context} → {ρ : ⟦ Γ ⟧} (dρ : ΔEnv Γ ρ) → ⟦ Γ ⟧
  update {Γ} {ρ} dρ = CA.update′ Γ ρ dρ

  apply-env : ∀ Γ → (ρ : ⟦ Γ ⟧) → (dρ : ΔEnv Γ ρ) → ⟦ Γ ⟧
  apply-env = CA.update′

  diff-env : ∀ Γ → (π ρ : ⟦ Γ ⟧) → ΔEnv Γ ρ
  diff-env = CA.diff′
