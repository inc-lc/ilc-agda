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
    {{validity-structure : Validity.Structure ⟦_⟧Base}}
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open Validity.Structure ⟦_⟧Base

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

  ⟦_⟧ΔVar : ∀ {τ Γ} → (x : Var Γ τ) → (ρ : ⟦ Γ ⟧) → Δ₍ Γ ₎ ρ → Δ₍ τ ₎ (⟦ x ⟧Var ρ)
  ⟦ this   ⟧ΔVar (v • ρ) (dv • dρ) = dv
  ⟦ that x ⟧ΔVar (v • ρ) (dv • dρ) = ⟦ x ⟧ΔVar ρ dρ

  ⟦_⟧Δ (const {τ} c) ρ dρ = nil₍ τ ₎ (⟦ c ⟧Const)
  ⟦_⟧Δ (var x) ρ dρ = ⟦ x ⟧ΔVar ρ dρ
  ⟦_⟧Δ (app {σ} {τ} s t) ρ dρ =
       call-change {σ} {τ} (⟦ s ⟧Δ ρ dρ) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)
  ⟦_⟧Δ (abs {σ} {τ} t) ρ dρ = record
    { apply = λ v dv → ⟦ t ⟧Δ (v • ρ) (dv • dρ)
    ; correct = λ v dv →
      begin
        ⟦ t ⟧ (v ⊞₍ σ ₎ dv • ρ)  ⊞₍ τ ₎
        ⟦ t ⟧Δ (v ⊞₍ σ ₎ dv • ρ) (nil₍ σ ₎ (v ⊞₍ σ ₎ dv) • dρ)
      ≡⟨  correctness t (v ⊞₍ σ ₎ dv • ρ) (nil₍ σ ₎ (v ⊞₍ σ ₎ dv) • dρ) ⟩
        ⟦ t ⟧ (after-env (nil₍ σ ₎ (v ⊞₍ σ ₎ dv) • dρ))
      ≡⟨⟩
        ⟦ t ⟧ (((v ⊞₍ σ ₎ dv) ⊞₍ σ ₎ nil₍ σ ₎ (v ⊞₍ σ ₎ dv)) • after-env dρ)
      ≡⟨  cong (λ hole → ⟦ t ⟧ (hole • after-env dρ)) (update-nil₍ σ ₎ (v ⊞₍ σ ₎ dv))  ⟩
        ⟦ t ⟧ (v ⊞₍ σ ₎ dv • after-env dρ)
      ≡⟨⟩
        ⟦ t ⟧ (after-env (dv • dρ))
      ≡⟨  sym (correctness t (v • ρ) (dv • dρ))  ⟩
        ⟦ t ⟧ (v • ρ)  ⊞₍ τ ₎  ⟦ t ⟧Δ (v • ρ) (dv • dρ)
      ∎
    } where open ≡-Reasoning

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
  correctness {σ ⇒ τ} {Γ} (abs t) ρ dρ = ext (λ v →
    let
      -- dρ′ : ΔEnv (σ • Γ) (v • ρ)
      dρ′ = nil₍ σ ₎ v • dρ
    in
      begin
        ⟦ t ⟧ (v • ρ) ⊞₍ τ ₎ ⟦ t ⟧Δ _ dρ′
      ≡⟨ correctness {τ} t _ dρ′ ⟩
        ⟦ t ⟧ (after-env dρ′)
      ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • after-env dρ)) (update-nil₍ σ ₎ v) ⟩
        ⟦ t ⟧ (v • after-env dρ)
      ∎
    ) where open ≡-Reasoning

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
