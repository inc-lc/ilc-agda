------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Connecting Parametric.Change.Term and Parametric.Change.Value.
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value
import Parametric.Denotation.Evaluation as Evaluation
import Parametric.Change.Type as ChangeType
import Parametric.Change.Term as ChangeTerm
import Parametric.Change.Value as ChangeValue

module Parametric.Change.Evaluation
    {Base : Type.Structure}
    {Const : Term.Structure Base}
    (⟦_⟧Base : Value.Structure Base)
    (⟦_⟧Const : Evaluation.Structure Const ⟦_⟧Base)
    (ΔBase : ChangeType.Structure Base)
    (apply-base : ChangeTerm.ApplyStructure Const ΔBase)
    (diff-base : ChangeTerm.DiffStructure Const ΔBase)
    (⟦apply-base⟧ : ChangeValue.ApplyStructure Const ⟦_⟧Base ΔBase)
    (⟦diff-base⟧ : ChangeValue.DiffStructure Const ⟦_⟧Base ΔBase)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open ChangeType.Structure Base ΔBase
open ChangeTerm.Structure Const ΔBase apply-base diff-base
open ChangeValue.Structure Const ⟦_⟧Base ΔBase ⟦apply-base⟧ ⟦diff-base⟧

open import Relation.Binary.PropositionalEquality
open import Base.Denotation.Notation
open import Postulate.Extensionality

-- Extension point 1: Relating ⊕ and its value on base types
ApplyStructure : Set
ApplyStructure = ∀ ι {Γ} →
  {t : Term Γ (base ι)} {Δt : Term Γ (ΔType (base ι))} {ρ : ⟦ Γ ⟧} →
  ⟦ t ⟧ ρ ⟦⊕₍ base ι ₎⟧ ⟦ Δt ⟧ ρ ≡ ⟦ t ⊕₍ base ι ₎ Δt ⟧ ρ

-- Extension point 2: Relating ⊝ and its value on base types
DiffStructure : Set
DiffStructure = ∀ ι {Γ} →
  {s : Term Γ (base ι)} {t : Term Γ (base ι)} {ρ : ⟦ Γ ⟧} →
  ⟦ s ⟧ ρ ⟦⊝₍ base ι ₎⟧ ⟦ t ⟧ ρ ≡ ⟦ s ⊝₍ base ι ₎ t ⟧ ρ

module Structure
    (meaning-⊕-base : ApplyStructure)
    (meaning-⊝-base : DiffStructure)
  where

  -- unique names with unambiguous types
  -- to help type inference figure things out
  private
    module Disambiguation where
      infixr 9 _⋆_
      _⋆_ : Type → Context → Context
      _⋆_ = _•_

  -- We provide: Relating ⊕ and ⊝ and their values on arbitrary types.
  meaning-⊕ : ∀ {τ Γ}
    {t : Term Γ τ} {Δt : Term Γ (ΔType τ)} {ρ : ⟦ Γ ⟧} →
    ⟦ t ⟧ ρ ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ ≡ ⟦ t ⊕₍ τ ₎ Δt ⟧ ρ

  meaning-⊝ : ∀ {τ Γ}
    {s : Term Γ τ} {t : Term Γ τ} {ρ : ⟦ Γ ⟧} →
    ⟦ s ⟧ ρ ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ ≡ ⟦ s ⊝₍ τ ₎ t ⟧ ρ

  meaning-⊕ {base ι} {Γ} {τ} {Δt} {ρ} = meaning-⊕-base ι {Γ} {τ} {Δt} {ρ}
  meaning-⊕ {σ ⇒ τ} {Γ} {t} {Δt} {ρ} = ext (λ v →
    let
      Γ′ = σ ⋆ (σ ⇒ τ) ⋆ ΔType (σ ⇒ τ) ⋆ Γ
      ρ′ : ⟦ Γ′ ⟧
      ρ′ = v • (⟦ t ⟧ ρ) • (⟦ Δt ⟧ ρ) • ρ
      x  : Term Γ′ σ
      x  = var this
      f  : Term Γ′ (σ ⇒ τ)
      f  = var (that this)
      Δf : Term Γ′ (ΔType (σ ⇒ τ))
      Δf = var (that (that this))
      y  = app f x
      Δy = app (app Δf x) (x ⊝ x)
    in
      begin
        ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v (v ⟦⊝₍ σ ₎⟧ v)
      ≡⟨ cong (λ hole → ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v hole)
           (meaning-⊝ {s = x} {x} {ρ′}) ⟩
        ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v (⟦ x ⊝ x ⟧ ρ′)
      ≡⟨ meaning-⊕ {t = y} {Δt = Δy} {ρ′} ⟩
        ⟦ y ⊕₍ τ ₎ Δy ⟧ ρ′
      ∎)
    where
      open ≡-Reasoning
      open Disambiguation

  meaning-⊝ {base ι} {Γ} {s} {t} {ρ} = meaning-⊝-base ι {Γ} {s} {t} {ρ}
  meaning-⊝ {σ ⇒ τ} {Γ} {s} {t} {ρ} =
    ext (λ v → ext (λ Δv →
    let
      Γ′ = ΔType σ ⋆ σ ⋆ (σ ⇒ τ) ⋆ (σ ⇒ τ) ⋆ Γ
      ρ′ : ⟦ Γ′ ⟧Context
      ρ′ = Δv • v • ⟦ t ⟧Term ρ • ⟦ s ⟧Term ρ • ρ
      Δx : Term Γ′ (ΔType σ)
      Δx = var this
      x  : Term Γ′ σ
      x  = var (that this)
      f  : Term Γ′ (σ ⇒ τ)
      f  = var (that (that this))
      g  : Term Γ′ (σ ⇒ τ)
      g  = var (that (that (that this)))
      y  = app f x
      y′ = app g (x ⊕₍ σ ₎ Δx)
    in
      begin
        ⟦ s ⟧ ρ (v ⟦⊕₍ σ ₎⟧ Δv) ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ v
      ≡⟨ cong (λ hole → ⟦ s ⟧ ρ hole ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ v)
           (meaning-⊕ {t = x} {Δt = Δx} {ρ′}) ⟩
        ⟦ s ⟧ ρ (⟦ x ⊕₍ σ ₎ Δx ⟧ ρ′) ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ v
      ≡⟨ meaning-⊝ {s = y′} {y} {ρ′} ⟩
        ⟦ y′ ⊝ y ⟧ ρ′
      ∎))
    where
      open ≡-Reasoning
      open Disambiguation
