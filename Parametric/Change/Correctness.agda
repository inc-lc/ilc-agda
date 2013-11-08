import Parametric.Syntax.Type as Type
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
    (diff-base : ChangeTerm.DiffStructure Const ΔBase)
    (apply-base : ChangeTerm.ApplyStructure Const ΔBase)
    (⟦apply-base⟧ : ChangeValue.ApplyStructure Const ⟦_⟧Base ΔBase)
    (⟦diff-base⟧ : ChangeValue.DiffStructure Const ⟦_⟧Base ΔBase)
    (meaning-⊕-base : ChangeEvaluation.ApplyStructure
      ⟦_⟧Base ⟦_⟧Const ΔBase apply-base diff-base ⟦apply-base⟧ ⟦diff-base⟧)
    (meaning-⊝-base : ChangeEvaluation.DiffStructure
      ⟦_⟧Base ⟦_⟧Const ΔBase apply-base diff-base ⟦apply-base⟧ ⟦diff-base⟧)
    (validity-structure : Validity.Structure ⟦_⟧Base)
    (specification-structure : Specification.Structure
      Const ⟦_⟧Base ⟦_⟧Const validity-structure)
    (derive-const : Derive.Structure Const ΔBase)
    (implementation-structure : Implementation.Structure
      Const ⟦_⟧Base ⟦_⟧Const ΔBase
      validity-structure specification-structure
      ⟦apply-base⟧ ⟦diff-base⟧ derive-const)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open Validity.Structure ⟦_⟧Base validity-structure
open Specification.Structure
  Const ⟦_⟧Base ⟦_⟧Const validity-structure specification-structure
open ChangeType.Structure Base ΔBase
open ChangeTerm.Structure Const ΔBase diff-base apply-base
open ChangeValue.Structure Const ⟦_⟧Base ΔBase ⟦apply-base⟧ ⟦diff-base⟧
open ChangeEvaluation.Structure
  ⟦_⟧Base ⟦_⟧Const ΔBase
  apply-base diff-base
  ⟦apply-base⟧ ⟦diff-base⟧
  meaning-⊕-base meaning-⊝-base
open Derive.Structure Const ΔBase derive-const
open Implementation.Structure
  Const ⟦_⟧Base ⟦_⟧Const ΔBase validity-structure specification-structure
  ⟦apply-base⟧ ⟦diff-base⟧ derive-const implementation-structure

-- The denotational properties of the `derive` transformation.
-- In particular, the main theorem about it producing the correct
-- incremental behavior.

open import Base.Denotation.Notation
open import Relation.Binary.PropositionalEquality
open import Postulate.Extensionality

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

  -- That `derive t` implements ⟦ t ⟧Δ
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

  -- Our main theorem, as we used to state it in the paper.
  main-theorem : ∀ {σ τ}
    {f : Term ∅ (σ ⇒ τ)} {x : Term ∅ σ} {y : Term ∅ σ}
    → ⟦ app f y ⟧
    ≡ ⟦ app f x ⊕₍ τ ₎ app (app (derive f) x) (y ⊝ x) ⟧

  main-theorem {σ} {τ} {f} {x} {y} =
    let
      h  = ⟦ f ⟧ ∅
      Δh = ⟦ f ⟧Δ ∅ ∅
      Δh′ = ⟦ derive f ⟧ ∅
      v  = ⟦ x ⟧ ∅
      u  = ⟦ y ⟧ ∅
      Δoutput-term = app (app (derive f) x) (y ⊝ x)
    in
      ext {A = ⟦ ∅ ⟧Context} (λ { ∅ →
      begin
        h u
      ≡⟨ cong h (sym (update-diff₍ σ ₎ u v)) ⟩
        h (v ⊞₍ σ ₎ (u ⊟₍ σ ₎ v))
      ≡⟨ corollary-closed {σ} {τ} f v (u ⊟₍ σ ₎ v) ⟩
        h v ⊞₍ τ ₎ call-change {σ} {τ} Δh v (u ⊟₍ σ ₎ v)
      ≡⟨ carry-over {τ}
         (call-change {σ} {τ} Δh v (u ⊟₍ σ ₎ v))
         (derive-correct f
           ∅ ∅ ∅ ∅ v (u ⊟₍ σ ₎ v) (u ⟦⊝₍ σ ₎⟧ v) (u⊟v≈u⊝v {σ} {u} {v})) ⟩
         h v ⟦⊕₍ τ ₎⟧ Δh′ v (u ⟦⊝₍ σ ₎⟧ v)
      ≡⟨ trans
         (cong (λ hole → h v ⟦⊕₍ τ ₎⟧ Δh′ v hole) (meaning-⊝ {σ} {s = y} {x}))
         (meaning-⊕ {t = app f x} {Δt = Δoutput-term}) ⟩
         ⟦ app f x ⊕₍ τ ₎ app (app (derive f) x) (y ⊝ x) ⟧ ∅
      ∎}) where open ≡-Reasoning

  -- A corollary, closer to what we state in the paper.
  main-theorem-coroll : ∀ {σ τ}
    {f : Term ∅ (σ ⇒ τ)} {x : Term ∅ σ} {dx : Term ∅ (ΔType σ)}
    → ⟦ app f (x ⊕₍ σ ₎ dx) ⟧
    ≡ ⟦ app f x ⊕₍ τ ₎ app (app (derive f) x) ((x ⊕₍ σ ₎ dx) ⊝ x) ⟧
  main-theorem-coroll {σ} {τ} {f} {x} {dx} = main-theorem {σ} {τ} {f} {x} {x ⊕₍ σ ₎ dx}

  -- For the statement in the paper, we'd need to talk about valid changes in
  -- the lambda calculus. In fact we can, thanks to the `implements` relation;
  -- but I guess the required proof must be done directly from derive-correct,
  -- not from main-theorem.
