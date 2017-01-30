------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Change evaluation (Def 3.6 and Fig. 4h).
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value
import Parametric.Denotation.Evaluation as Evaluation
import Parametric.Change.Validity as Validity

module Parametric.Change.Specification
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
    (⟦_⟧Const : Evaluation.Structure Const ⟦_⟧Base)
    {{validity-structure : Validity.Structure {Base} ⟦_⟧Base}}
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open Validity.Structure {Base} ⟦_⟧Base {{validity-structure}}

open import Base.Denotation.Notation
open import Relation.Binary.PropositionalEquality
open import Theorem.CongApp
open import Postulate.Extensionality

module Structure where
  ---------------
  -- Interface --
  ---------------

  -- We provide: Derivatives of terms.
  ⟦_⟧Δ : ∀ {τ Γ} → (t : Term Γ τ) (ρ : ⟦ Γ ⟧) (dρ : Δ₍ Γ ₎ ρ) → Δ₍ τ ₎ (⟦ t ⟧ ρ)

  -- And we provide correctness proofs about the derivatives.
  correctness : ∀ {τ Γ} (t : Term Γ τ) →
    IsDerivative₍ Γ , τ ₎ ⟦ t ⟧ ⟦ t ⟧Δ

  --------------------
  -- Implementation --
  --------------------
  open import Base.Change.Equivalence
  open import Base.Change.Equivalence.Realizers

  module _ {σ τ : Type} {Γ : Context} (t : Term (σ • Γ) τ) where
    instance
      cΓ : ChangeAlgebra ⟦ Γ ⟧Context
      cΓ = change-algebra₍ Γ ₎
      cσ : ChangeAlgebra ⟦ σ ⟧Type
      cσ = change-algebra σ
      cτ : ChangeAlgebra ⟦ τ ⟧Type
      cτ = change-algebra τ

    private
      ⟦⟧Δλ = nil {{changeAlgebraFun {{cΓ}} {{change-algebra₍ σ ⇒ τ ₎}}}} ⟦ abs t ⟧

    ⟦⟧Δλ-realizer : ∀
      (ρ : ⟦ Γ ⟧) (dρ : Δ₍ Γ ₎ ρ)
      (v : ⟦ σ ⟧) (dv : Δ₍ σ ₎ v) →
      Δ₍ τ ₎ (⟦ t ⟧ (v • ρ))
    ⟦⟧Δλ-realizer ρ dρ v dv = ⟦ t ⟧Δ (v • ρ) (dv • dρ)

    ⟦⟧Δλ-realizer-correct :
      equiv-hp-binary {{cΓ}} {{cσ}} {{cτ}} (⟦ abs t ⟧) ⟦⟧Δλ ⟦⟧Δλ-realizer
    ⟦⟧Δλ-realizer-correct ρ dρ v dv =
      begin
        ⟦ t ⟧ (v ⊞₍ σ ₎ dv • ρ ⊞₍ Γ ₎ dρ) ⊟₍ τ ₎ ⟦ t ⟧ (v • ρ)
      ≙⟨ equiv-cancel-2 {{change-algebra τ}}
           (⟦ t ⟧ (v ⊞₍ σ ₎ dv • ρ ⊞₍ Γ ₎ dρ))
           (⟦ t ⟧Δ (v • ρ) (dv • dρ))
           (sym (correctness t (v • ρ) (dv • dρ)))
      ⟩
         ⟦ t ⟧Δ (v • ρ) (dv • dρ)
      ∎ where open ≙-Reasoning

    ⟦_⟧Δλ′-faster = proj₁ (equiv-raw-change-to-change-binary {{cΓ}} {{cσ}} {{cτ}} ⟦ abs t ⟧ ⟦⟧Δλ ⟦⟧Δλ-realizer ⟦⟧Δλ-realizer-correct)
      where
        open import Data.Product

  ⟦_⟧ΔVar : ∀ {τ Γ} → (x : Var Γ τ) → (ρ : ⟦ Γ ⟧) → Δ₍ Γ ₎ ρ → Δ₍ τ ₎ (⟦ x ⟧Var ρ)
  ⟦ this   ⟧ΔVar (v • ρ) (dv • dρ) = dv
  ⟦ that x ⟧ΔVar (v • ρ) (dv • dρ) = ⟦ x ⟧ΔVar ρ dρ

  ⟦_⟧Δ (const {τ} c) ρ dρ = nil₍ τ ₎ (⟦ c ⟧Const)
  ⟦_⟧Δ (var x) ρ dρ = ⟦ x ⟧ΔVar ρ dρ
  ⟦_⟧Δ (app {σ} {τ} s t) ρ dρ =
       call-change {σ} {τ} (⟦ s ⟧Δ ρ dρ) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)
  ⟦_⟧Δ (abs {σ} {τ} t) ρ dρ = apply ⟦ t ⟧Δλ′-faster ρ dρ

  correctVar : ∀ {τ Γ} (x : Var Γ τ) →
    IsDerivative₍ Γ , τ ₎ ⟦ x ⟧ ⟦ x ⟧ΔVar
  correctVar (this) (v • ρ) (dv • dρ) = refl
  correctVar (that y) (v • ρ) (dv • dρ) = correctVar y ρ dρ

  correctness (const {τ} c) ρ dρ = update-nil₍ τ ₎ ⟦ c ⟧Const
  correctness {τ} (var x) ρ dρ = correctVar {τ} x ρ dρ
  correctness (app {σ} {τ} s t) ρ dρ =
    let
      f₁ = ⟦ s ⟧ ρ
      f₂ = ⟦ s ⟧ (after-env dρ)
      Δf = ⟦ s ⟧Δ ρ dρ
      u₁ = ⟦ t ⟧ ρ
      u₂ = ⟦ t ⟧ (after-env dρ)
      Δu = ⟦ t ⟧Δ ρ dρ
    in
      begin
        f₁ u₁ ⊞₍ τ ₎ call-change {σ} {τ} Δf u₁ Δu
      ≡⟨  sym (is-valid {σ} {τ} Δf u₁ Δu) ⟩
        (f₁ ⊞₍ σ ⇒ τ ₎ Δf) (u₁ ⊞₍ σ ₎ Δu)
      ≡⟨ correctness {σ ⇒ τ} s ρ dρ ⟨$⟩ correctness {σ} t ρ dρ ⟩
        f₂ u₂
      ∎ where open ≡-Reasoning
  correctness {σ ⇒ τ} {Γ} (abs t) ρ dρ = equiv-raw-deriv-to-deriv-binary {{change-algebra₍ Γ ₎}} {{change-algebra σ}} ⟦ abs t ⟧Term (⟦⟧Δλ-realizer t) (⟦⟧Δλ-realizer-correct t) ρ dρ

  -- Corollary: (f ⊞ df) (v ⊞ dv) = f v ⊞ df v dv

  corollary : ∀ {σ τ Γ}
    (s : Term Γ (σ ⇒ τ)) (t : Term Γ σ) (ρ : ⟦ Γ ⟧) (dρ : Δ₍ Γ ₎ ρ) →
      (⟦ s ⟧ ρ ⊞₍ σ ⇒ τ ₎ ⟦ s ⟧Δ ρ dρ)
        (⟦ t ⟧ ρ ⊞₍ σ ₎ ⟦ t ⟧Δ ρ dρ)
    ≡ (⟦ s ⟧ ρ) (⟦ t ⟧ ρ)
      ⊞₍ τ ₎
      (call-change {σ} {τ} (⟦ s ⟧Δ ρ dρ)) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)

  corollary {σ} {τ} s t ρ dρ =
    is-valid {σ} {τ} (⟦ s ⟧Δ ρ dρ) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)

  corollary-closed : ∀ {σ τ} (t : Term ∅ (σ ⇒ τ))
    (v : ⟦ σ ⟧) (dv : Δ₍ σ ₎ v)
    → ⟦ t ⟧ ∅ (after₍ σ ₎ dv)
    ≡ ⟦ t ⟧ ∅ v ⊞₍ τ ₎ call-change {σ} {τ} (⟦ t ⟧Δ ∅ ∅) v dv

  corollary-closed {σ} {τ} t v dv =
    let
      f  = ⟦ t ⟧ ∅
      Δf = ⟦ t ⟧Δ ∅ ∅
    in
      begin
        f (after₍ σ ₎ dv)
      ≡⟨ cong (λ hole → hole (after₍ σ ₎ dv))
              (sym (correctness {σ ⇒ τ} t ∅ ∅)) ⟩
         (f ⊞₍ σ ⇒ τ ₎ Δf) (after₍ σ ₎ dv)
      ≡⟨ is-valid {σ} {τ} (⟦ t ⟧Δ ∅ ∅) v dv ⟩
        f (before₍ σ ₎ dv) ⊞₍ τ ₎ call-change {σ} {τ} Δf v dv
      ∎ where open ≡-Reasoning
