------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Correctness of differentiation (Lemma 3.10 and Theorem 3.11).
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
open import Base.Data.DependentList
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value
import Parametric.Denotation.Evaluation as Evaluation
import Parametric.Change.Validity as Validity
import Parametric.Change.Specification as Specification
import Parametric.Change.Type as ChangeType
import Parametric.Change.Term as ChangeTerm
import Parametric.Change.Value as ChangeValue
import Parametric.Change.Evaluation as ChangeEvaluation
import Parametric.Change.Derive as Derive
import Parametric.Change.Implementation as Implementation

module Parametric.Change.Correctness
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
    (⟦_⟧Const : Evaluation.Structure Const ⟦_⟧Base)
    (ΔBase : ChangeType.Structure Base)
    (apply-base : ChangeTerm.ApplyStructure Const ΔBase)
    (diff-base : ChangeTerm.DiffStructure Const ΔBase)
    (nil-base : ChangeTerm.NilStructure Const ΔBase)
    (⟦apply-base⟧ : ChangeValue.ApplyStructure Const ⟦_⟧Base ΔBase)
    (⟦diff-base⟧ : ChangeValue.DiffStructure Const ⟦_⟧Base ΔBase)
    (⟦nil-base⟧ : ChangeValue.NilStructure Const ⟦_⟧Base ΔBase)
    (meaning-⊕-base : ChangeEvaluation.ApplyStructure
      ⟦_⟧Base ⟦_⟧Const ΔBase apply-base diff-base nil-base ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧)
    (meaning-⊝-base : ChangeEvaluation.DiffStructure
      ⟦_⟧Base ⟦_⟧Const ΔBase apply-base diff-base nil-base ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧)
    (meaning-onil-base : ChangeEvaluation.NilStructure
      ⟦_⟧Base ⟦_⟧Const ΔBase apply-base diff-base nil-base ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧)
    {{validity-structure : Validity.Structure ⟦_⟧Base}}
    (specification-structure : Specification.Structure
      Const ⟦_⟧Base ⟦_⟧Const)
    (derive-const : Derive.Structure Const ΔBase)
    (implementation-structure : Implementation.Structure
      Const ⟦_⟧Base ⟦_⟧Const ΔBase
      specification-structure
      ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧ derive-const)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open Validity.Structure ⟦_⟧Base
open Specification.Structure specification-structure
open ChangeType.Structure Base ΔBase
open ChangeTerm.Structure Const ΔBase apply-base diff-base nil-base
open ChangeValue.Structure Const ⟦_⟧Base ΔBase ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧
open ChangeEvaluation.Structure
  ⟦_⟧Base ⟦_⟧Const ΔBase
  apply-base diff-base nil-base
  ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧
  meaning-⊕-base meaning-⊝-base meaning-onil-base
open Derive.Structure Const ΔBase derive-const
open Implementation.Structure implementation-structure
-- The denotational properties of the `derive` transformation.
-- In particular, the main theorem about it producing the correct
-- incremental behavior.

open import Base.Denotation.Notation
open import Relation.Binary.PropositionalEquality
open import Postulate.Extensionality

-- Extension point: A proof that change evaluation for a fully
-- applied primitive is related to the value of incrementalizing
-- this primitive, if their arguments are so related.
Structure : Set
Structure = ∀ {Σ Γ τ} (c : Const Σ τ) (ts : Terms Γ Σ)
  (ρ : ⟦ Γ ⟧) (dρ : Δ₍ Γ ₎ ρ) (ρ′ : ⟦ mapContext ΔType Γ ⟧) (dρ≈ρ′ : implements-env Γ dρ ρ′) →
  (ts-correct : implements-env Σ (⟦ ts ⟧ΔTerms ρ dρ) (⟦ derive-terms ts ⟧Terms (alternate ρ ρ′))) →
  ⟦ c ⟧ΔConst (⟦ ts ⟧Terms ρ) (⟦ ts ⟧ΔTerms ρ dρ) ≈₍ τ ₎ ⟦ derive-const c (fit-terms ts) (derive-terms ts) ⟧ (alternate ρ ρ′)

module Structure (derive-const-correct : Structure) where
  deriveVar-correct : ∀ {τ Γ} (x : Var Γ τ)
    (ρ : ⟦ Γ ⟧) (dρ : Δ₍ Γ ₎ ρ) (ρ′ : ⟦ mapContext ΔType Γ ⟧) (dρ≈ρ′ : implements-env Γ dρ ρ′) →
    ⟦ x ⟧ΔVar ρ dρ ≈₍ τ ₎ ⟦ deriveVar x ⟧ (alternate ρ ρ′)
  deriveVar-correct this (v • ρ) (dv • dρ) (dv′ • dρ′) (dv≈dv′ • dρ≈dρ′) = dv≈dv′
  deriveVar-correct (that x) (v • ρ) (dv • dρ) (dv′ • dρ′) (dv≈dv′ • dρ≈dρ′) = deriveVar-correct x ρ dρ dρ′ dρ≈dρ′

  -- We provide: A variant of Lemma 3.10 for arbitrary contexts.
  derive-correct : ∀ {τ Γ} (t : Term Γ τ)
    (ρ : ⟦ Γ ⟧) (dρ : Δ₍ Γ ₎ ρ) (ρ′ : ⟦ mapContext ΔType Γ ⟧) (dρ≈ρ′ : implements-env Γ dρ ρ′) →
    ⟦ t ⟧Δ ρ dρ ≈₍ τ ₎ ⟦ derive t ⟧ (alternate ρ ρ′)

  derive-terms-correct : ∀ {Σ Γ} (ts : Terms Γ Σ)
    (ρ : ⟦ Γ ⟧) (dρ : Δ₍ Γ ₎ ρ) (ρ′ : ⟦ mapContext ΔType Γ ⟧) (dρ≈ρ′ : implements-env Γ dρ ρ′) →
    implements-env Σ (⟦ ts ⟧ΔTerms ρ dρ) (⟦ derive-terms ts ⟧Terms (alternate ρ ρ′))

  derive-terms-correct ∅ ρ dρ ρ′ dρ≈ρ′ = ∅
  derive-terms-correct (t • ts) ρ dρ ρ′ dρ≈ρ′ =
    derive-correct t ρ dρ ρ′ dρ≈ρ′ • derive-terms-correct ts ρ dρ ρ′ dρ≈ρ′

  derive-correct (const c ts) ρ dρ ρ′ dρ≈ρ′ =
    derive-const-correct c ts ρ dρ ρ′ dρ≈ρ′
      (derive-terms-correct ts ρ dρ ρ′ dρ≈ρ′)
  derive-correct (var x) ρ dρ ρ′ dρ≈ρ′ =
    deriveVar-correct x ρ dρ ρ′ dρ≈ρ′
  derive-correct (app {σ} {τ} s t) ρ dρ ρ′ dρ≈ρ′
   = subst (λ ⟦t⟧ → ⟦ app s t ⟧Δ ρ dρ ≈₍ τ ₎ (⟦ derive s ⟧Term (alternate ρ ρ′)) ⟦t⟧ (⟦ derive t ⟧Term (alternate ρ ρ′))) (⟦fit⟧ t ρ ρ′)
       (derive-correct {σ ⇒ τ} s ρ dρ ρ′ dρ≈ρ′
          (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ) (⟦ derive t ⟧ (alternate ρ ρ′)) (derive-correct {σ} t ρ dρ ρ′ dρ≈ρ′))

  derive-correct (abs {σ} {τ} t) ρ dρ ρ′ dρ≈ρ′ =
    λ w dw w′ dw≈w′ →
      derive-correct t (w • ρ) (dw • dρ) (w′ • ρ′) (dw≈w′ • dρ≈ρ′)

  derive-correct-closed : ∀ {τ} (t : Term ∅ τ) →
    ⟦ t ⟧Δ ∅ ∅ ≈₍ τ ₎ ⟦ derive t ⟧ ∅

  derive-correct-closed t = derive-correct t ∅ ∅ ∅ ∅

  -- And we proof Theorem 3.11, finally.
  main-theorem : ∀ {σ τ}
    {f : Term ∅ (σ ⇒ τ)} {s : Term ∅ σ} {ds : Term ∅ (ΔType σ)} →
    {dv : Δ₍ σ ₎ (⟦ s ⟧ ∅)} {erasure : dv ≈₍ σ ₎ (⟦ ds ⟧ ∅)} →

    ⟦ app f (s ⊕₍ σ ₎ ds) ⟧ ≡ ⟦ app f s ⊕₍ τ ₎ app (app (derive f) s) ds ⟧

  main-theorem {σ} {τ} {f} {s} {ds} {dv} {erasure} =
    let
      g  = ⟦ f ⟧ ∅
      Δg = ⟦ f ⟧Δ ∅ ∅
      Δg′ = ⟦ derive f ⟧ ∅
      v  = ⟦ s ⟧ ∅
      dv′ = ⟦ ds ⟧ ∅
      u  = ⟦ s ⊕₍ σ ₎ ds ⟧ ∅
      -- Δoutput-term = app (app (derive f) x) (y ⊝ x)
    in
      ext {A = ⟦ ∅ ⟧Context} (λ { ∅ →
      begin
        g u
      ≡⟨ cong g (sym (meaning-⊕ {t = s} {Δt = ds})) ⟩
        g (v ⟦⊕₍ σ ₎⟧ dv′)
      ≡⟨ cong g (sym (carry-over {σ} dv erasure)) ⟩
        g (v ⊞₍ σ ₎ dv)
      ≡⟨ corollary-closed {σ} {τ} f v dv ⟩
        g v ⊞₍ τ ₎ call-change {σ} {τ} Δg v dv
      ≡⟨ carry-over {τ} (call-change {σ} {τ} Δg v dv)
           (derive-correct-closed f v dv dv′ erasure) ⟩
        g v ⟦⊕₍ τ ₎⟧ Δg′ v dv′
      ≡⟨ meaning-⊕ {t = app f s} {Δt = app (app (derive f) s) ds} ⟩
        ⟦ app f s ⊕₍ τ ₎ app (app (derive f) s) ds ⟧ ∅
      ∎}) where open ≡-Reasoning
