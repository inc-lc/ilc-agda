------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- The values of terms in Parametric.Change.Term.
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
open import Base.Data.DependentList
import Parametric.Denotation.Value as Value
import Parametric.Change.Type as ChangeType

module Parametric.Change.Value
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
    (ΔBase : ChangeType.Structure Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open ChangeType.Structure Base ΔBase

open import Base.Denotation.Notation

-- Extension point 1: The value of ⊕ for base types.
ApplyStructure : Set
ApplyStructure = ∀ ι → ⟦ ι ⟧Base → ⟦ ΔBase ι ⟧Type → ⟦ ι ⟧Base

-- Extension point 2: The value of ⊝ for base types.
DiffStructure : Set
DiffStructure = ∀ ι → ⟦ ι ⟧Base → ⟦ ι ⟧Base → ⟦ ΔBase ι ⟧Type

NilStructure : Set
NilStructure = ∀ ι → ⟦ ι ⟧Base → ⟦ ΔBase ι ⟧Type

module Structure
    (⟦apply-base⟧ : ApplyStructure)
    (⟦diff-base⟧ : DiffStructure)
    (⟦nil-base⟧ : NilStructure)
  where

  -- We provide: The value of ⊕ and ⊝ for arbitrary types.
  ⟦apply⟧ : ∀ τ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
  ⟦diff⟧ : ∀ τ → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧
  ⟦nil₍_₎⟧ : ∀ τ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧

  infixl 6 ⟦apply⟧ ⟦diff⟧
  syntax ⟦apply⟧ τ v dv = v ⟦⊕₍ τ ₎⟧ dv
  syntax ⟦diff⟧ τ u v = u ⟦⊝₍ τ ₎⟧ v

  v ⟦⊕₍ base ι ₎⟧ Δv = ⟦apply-base⟧ ι v Δv
  f ⟦⊕₍ σ ⇒ τ ₎⟧ Δf = λ v → f v ⟦⊕₍ τ ₎⟧ Δf v (⟦nil₍ σ ₎⟧ v)

  u ⟦⊝₍ base ι ₎⟧ v = ⟦diff-base⟧ ι u v
  g ⟦⊝₍ σ ⇒ τ ₎⟧ f = λ v Δv → (g (v ⟦⊕₍ σ ₎⟧ Δv)) ⟦⊝₍ τ ₎⟧ (f v)

  ⟦nil₍ base ι ₎⟧ v = ⟦nil-base⟧ ι v
  ⟦nil₍ σ ⇒ τ ₎⟧ f = f ⟦⊝₍ σ ⇒ τ ₎⟧ f

  _⟦⊕⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
  _⟦⊕⟧_ {τ} = ⟦apply⟧ τ

  _⟦⊝⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧
  _⟦⊝⟧_ {τ} = ⟦diff⟧ τ

  ⟦nil⟧ : ∀ {τ} → ⟦ τ ⟧ → ⟦ ΔType τ ⟧
  ⟦nil⟧ {τ} = ⟦nil₍ τ ₎⟧

  alternate : ∀ {Γ} → ⟦ Γ ⟧ → ⟦ mapContext ΔType Γ ⟧ → ⟦ ΔContext Γ ⟧
  alternate {∅} ∅ ∅ = ∅
  alternate {τ • Γ} (v • ρ) (dv • dρ) = dv • v • alternate ρ dρ
