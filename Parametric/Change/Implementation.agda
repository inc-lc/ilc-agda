------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Logical relation for erasure (Def. 3.8 and Lemma 3.9)
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value
import Parametric.Denotation.Evaluation as Evaluation
import Parametric.Change.Validity as Validity
import Parametric.Change.Specification as Specification
import Parametric.Change.Type as ChangeType
import Parametric.Change.Value as ChangeValue
import Parametric.Change.Derive as Derive

module Parametric.Change.Implementation
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
    (⟦_⟧Const : Evaluation.Structure Const ⟦_⟧Base)
    (ΔBase : ChangeType.Structure Base)
    (validity-structure : Validity.Structure ⟦_⟧Base)
    (specification-structure : Specification.Structure
       Const ⟦_⟧Base ⟦_⟧Const validity-structure)
    (⟦apply-base⟧ : ChangeValue.ApplyStructure Const ⟦_⟧Base ΔBase)
    (⟦diff-base⟧ : ChangeValue.DiffStructure Const ⟦_⟧Base ΔBase)
    (derive-const : Derive.Structure Const ΔBase)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open Validity.Structure ⟦_⟧Base validity-structure
open Specification.Structure
  Const ⟦_⟧Base ⟦_⟧Const validity-structure specification-structure
open ChangeType.Structure Base ΔBase
open ChangeValue.Structure Const ⟦_⟧Base ΔBase ⟦apply-base⟧ ⟦diff-base⟧
open Derive.Structure Const ΔBase derive-const

open import Base.Denotation.Notation

open import Relation.Binary.PropositionalEquality
open import Postulate.Extensionality

record Structure : Set₁ where

  ----------------
  -- Parameters --
  ----------------

  field
    -- Extension point 1: Logical relation on base types.
    --
    -- In the paper, we assume that the logical relation is equality on base types
    -- (see Def. 3.8a). Here, we only require that plugins define what the logical
    -- relation is on base types, and provide proofs for the two extension points
    -- below.
    implements-base : ∀ ι {v : ⟦ ι ⟧Base} → Δ₍ ι ₎ v → ⟦ ΔBase ι ⟧Base → Set

    -- Extension point 2: Differences on base types are logically related.
    u⊟v≈u⊝v-base : ∀ ι {u v : ⟦ ι ⟧Base} →
      implements-base ι (u ⊟₍ ι ₎ v) (⟦diff-base⟧ ι u v)

    -- Extension point 3: Lemma 3.1 for base types.
    carry-over-base : ∀ {ι}
      {v : ⟦ ι ⟧Base}
      (Δv : Δ₍ ι ₎ v)
      {Δv′ : ⟦ ΔBase ι ⟧Base} (Δv≈Δv′ : implements-base ι Δv Δv′) →
        v ⊞₍ base ι ₎ Δv ≡ v ⟦⊕₍ base ι ₎⟧ Δv′

  ------------------------
  -- Logical relation ≈ --
  ------------------------

  infix 4 implements
  syntax implements τ u v = u ≈₍ τ ₎ v
  implements : ∀ τ {v} → Δ₍ τ ₎ v → ⟦ ΔType τ ⟧ → Set

  implements (base ι) Δf Δf′ = implements-base ι Δf Δf′
  implements (σ ⇒ τ) {f} Δf Δf′ =
    (w : ⟦ σ ⟧) (Δw : Δ₍ σ ₎ w)
    (Δw′ : ⟦ ΔType σ ⟧) (Δw≈Δw′ : implements σ {w} Δw Δw′) →
    implements τ {f w} (call-change {σ} {τ} Δf w Δw) (Δf′ w Δw′)

  infix 4 _≈_
  _≈_ : ∀ {τ v} → Δ₍ τ ₎ v → ⟦ ΔType τ ⟧ → Set
  _≈_ {τ} {v} = implements τ {v}

  data implements-env : ∀ Γ → {ρ : ⟦ Γ ⟧} (dρ : Δ₍ Γ ₎ ρ) → ⟦ mapContext ΔType Γ ⟧ → Set where
    ∅ : implements-env ∅ {∅} ∅ ∅
    _•_ : ∀ {τ Γ v ρ dv dρ v′ ρ′} →
      (dv≈v′ : implements τ {v} dv v′) →
      (dρ≈ρ′ : implements-env Γ {ρ} dρ ρ′) →
      implements-env (τ • Γ) {v • ρ} (dv • dρ) (v′ • ρ′)

  ----------------
  -- carry-over --
  ----------------

  -- This is lemma 3.10.
  carry-over : ∀ {τ}
    {v : ⟦ τ ⟧}
    (Δv : Δ₍ τ ₎ v)
    {Δv′ : ⟦ ΔType τ ⟧} (Δv≈Δv′ : Δv ≈₍ τ ₎ Δv′) →
      after₍ τ ₎ Δv ≡ before₍ τ ₎ Δv ⟦⊕₍ τ ₎⟧ Δv′

  u⊟v≈u⊝v : ∀ {τ : Type} {u v : ⟦ τ ⟧} →
    u ⊟₍ τ ₎ v ≈₍ τ ₎ u ⟦⊝₍ τ ₎⟧ v

  u⊟v≈u⊝v {base ι} {u} {v} = u⊟v≈u⊝v-base ι {u} {v}
  u⊟v≈u⊝v {σ ⇒ τ} {g} {f} = result where
    result : (w : ⟦ σ ⟧) (Δw : Δ₍ σ ₎ w) →
      (Δw′ : ⟦ ΔType σ ⟧) → Δw ≈₍ σ ₎ Δw′ →
        (g (after₍ σ ₎ Δw) ⊟₍ τ ₎ f (before₍ σ ₎ Δw)) ≈₍ τ ₎ g (before₍ σ ₎ Δw ⟦⊕₍ σ ₎⟧ Δw′) ⟦⊝₍ τ ₎⟧ f (before₍ σ ₎ Δw)
    result w Δw Δw′ Δw≈Δw′
      rewrite carry-over {σ} Δw Δw≈Δw′ =
      u⊟v≈u⊝v {τ} {g (before₍ σ ₎ Δw ⟦⊕₍ σ ₎⟧ Δw′)} {f (before₍ σ ₎ Δw)}

  carry-over {base ι} Δv Δv≈Δv′ = carry-over-base Δv Δv≈Δv′
  carry-over {σ ⇒ τ} {f} Δf {Δf′} Δf≈Δf′ =
    ext (λ v →
      carry-over {τ} {f v} (call-change {σ} {τ} Δf v (nil₍ σ ₎ v))
        {Δf′ v (v ⟦⊝₍ σ ₎⟧ v)}
        (Δf≈Δf′ v (nil₍ σ ₎ v) (v ⟦⊝₍ σ ₎⟧ v) ( u⊟v≈u⊝v {σ} {v} {v})))

  -- A property relating `alternate` and the subcontext relation Γ≼ΔΓ
  ⟦Γ≼ΔΓ⟧ : ∀ {Γ} (ρ : ⟦ Γ ⟧) (dρ : ⟦ mapContext ΔType Γ ⟧) →
    ρ ≡ ⟦ Γ≼ΔΓ ⟧ (alternate ρ dρ)
  ⟦Γ≼ΔΓ⟧ ∅ ∅ = refl
  ⟦Γ≼ΔΓ⟧ (v • ρ) (dv • dρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ ρ dρ)

  -- A specialization of the soundness of weakening
  ⟦fit⟧ : ∀ {τ Γ} (t : Term Γ τ) (ρ : ⟦ Γ ⟧) (dρ : ⟦ mapContext ΔType Γ ⟧) →
    ⟦ t ⟧ ρ ≡ ⟦ fit t ⟧ (alternate ρ dρ)
  ⟦fit⟧ t ρ dρ =
    trans (cong ⟦ t ⟧ (⟦Γ≼ΔΓ⟧ ρ dρ)) (sym (weaken-sound t _))
