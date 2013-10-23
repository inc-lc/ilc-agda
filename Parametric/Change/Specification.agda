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
    (validity-structure : Validity.Structure ⟦_⟧Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open Validity.Structure ⟦_⟧Base validity-structure

-- Denotation-as-specification
--
-- Contents
-- - ⟦_⟧Δ : binding-time-shifted derive
-- - Validity and correctness lemmas for ⟦_⟧Δ
-- - `corollary`: ⟦_⟧Δ reacts to both environment and arguments
-- - `corollary-closed`: binding-time-shifted main theorem

open import Base.Denotation.Notation
open import Relation.Binary.PropositionalEquality
-- open import Data.Integer
-- open import Theorem.Groups-Popl14
open import Theorem.CongApp
open import Postulate.Extensionality

record Structure : Set₁ where
  ----------------
  -- Parameters --
  ----------------

  field
    ⟦_⟧ΔConst : ∀ {Σ τ} → (c  : Const Σ τ) (ρ : ⟦ Σ ⟧) → ΔEnv Σ ρ → Change τ (⟦ c ⟧Const ρ)

    correctness-const : ∀ {Σ τ} (c : Const Σ τ) (ρ : ⟦ Σ ⟧) (dρ : ΔEnv Σ ρ)
      → after₍ τ ₎ (⟦ c ⟧ΔConst ρ dρ) ≡ ⟦ c ⟧Const (update dρ)

  ---------------
  -- Interface --
  ---------------

  ⟦_⟧Δ : ∀ {τ Γ} → (t : Term Γ τ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) → Change τ (⟦ t ⟧ ρ)
  ⟦_⟧ΔTerms : ∀ {Σ Γ} → (ts : Terms Γ Σ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) → ΔEnv Σ (⟦ ts ⟧Terms ρ)

  correctness : ∀ {τ Γ} (t : Term Γ τ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ)
    → after₍ τ ₎ (⟦ t ⟧Δ ρ dρ) ≡ ⟦ t ⟧ (update dρ)

  correctness-terms : ∀ {Σ Γ} (ts : Terms Γ Σ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ)
    → update (⟦ ts ⟧ΔTerms ρ dρ) ≡ ⟦ ts ⟧Terms (update dρ)

  --------------------
  -- Implementation --
  --------------------

  ⟦_⟧ΔVar : ∀ {τ Γ} → (x : Var Γ τ) → (ρ : ⟦ Γ ⟧) → ΔEnv Γ ρ → Change τ (⟦ x ⟧Var ρ)
  ⟦ this   ⟧ΔVar (v • ρ) (dv • dρ) = dv
  ⟦ that x ⟧ΔVar (v • ρ) (dv • dρ) = ⟦ x ⟧ΔVar ρ dρ

  ⟦_⟧Δ (const c ts) ρ dρ = ⟦ c ⟧ΔConst (⟦ ts ⟧Terms ρ) (⟦ ts ⟧ΔTerms ρ dρ)
  ⟦_⟧Δ (var x) ρ dρ = ⟦ x ⟧ΔVar ρ dρ
  ⟦_⟧Δ (app {σ} {τ} s t) ρ dρ =
       call-change {σ} {τ} (⟦ s ⟧Δ ρ dρ) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)
  ⟦_⟧Δ (abs {σ} {τ} t) ρ dρ = cons
    (λ v dv → ⟦ t ⟧Δ (v • ρ) (dv • dρ))
    (λ v dv →
      begin
        ⟦ t ⟧ (v ⊞₍ σ ₎ dv • ρ)  ⊞₍ τ ₎
        ⟦ t ⟧Δ (v ⊞₍ σ ₎ dv • ρ) (nil-change σ (v ⊞₍ σ ₎ dv) • dρ)
      ≡⟨  correctness t (v ⊞₍ σ ₎ dv • ρ) (nil-change σ (v ⊞₍ σ ₎ dv) • dρ) ⟩
        ⟦ t ⟧ (update (nil-change σ (v ⊞₍ σ ₎ dv) • dρ))
      ≡⟨⟩
        ⟦ t ⟧ (((v ⊞₍ σ ₎ dv) ⊞₍ σ ₎ nil-change σ (v ⊞₍ σ ₎ dv)) • update dρ)
      ≡⟨  cong (λ hole → ⟦ t ⟧ (hole • update dρ)) (v+[u-v]=u {σ})  ⟩
        ⟦ t ⟧ (v ⊞₍ σ ₎ dv • update dρ)
      ≡⟨⟩
        ⟦ t ⟧ (update (dv • dρ))
      ≡⟨  sym (correctness t (v • ρ) (dv • dρ))  ⟩
        ⟦ t ⟧ (v • ρ)  ⊞₍ τ ₎  ⟦ t ⟧Δ (v • ρ) (dv • dρ)
      ∎) where open ≡-Reasoning

  ⟦ ∅ ⟧ΔTerms ρ dρ = ∅
  ⟦ t • ts ⟧ΔTerms ρ dρ = ⟦ t ⟧Δ ρ dρ • ⟦ ts ⟧ΔTerms ρ dρ

  correctVar : ∀ {τ Γ} (x : Var Γ τ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) →
    ⟦ x ⟧ ρ ⊞₍ τ ₎ ⟦ x ⟧ΔVar ρ dρ ≡ ⟦ x ⟧ (update dρ)
  correctVar (this) (v • ρ) (dv • dρ) = refl
  correctVar (that y) (v • ρ) (dv • dρ) = correctVar y ρ dρ

  correctness-terms ∅ ρ dρ = refl
  correctness-terms (t • ts) ρ dρ =
    cong₂ _•_
      (correctness t ρ dρ)
      (correctness-terms ts ρ dρ)

  correctness (const {Σ} {τ} c ts) ρ dρ =
    begin
      after₍ τ ₎ (⟦ c ⟧ΔConst (⟦ ts ⟧Terms ρ) (⟦ ts ⟧ΔTerms ρ dρ))
    ≡⟨ correctness-const c (⟦ ts ⟧Terms ρ) (⟦ ts ⟧ΔTerms ρ dρ) ⟩
      ⟦ c ⟧Const (update (⟦ ts ⟧ΔTerms ρ dρ))
    ≡⟨ cong ⟦ c ⟧Const (correctness-terms ts ρ dρ) ⟩
      ⟦ c ⟧Const (⟦ ts ⟧Terms (update dρ))
    ∎ where open ≡-Reasoning
  correctness {τ} (var x) ρ dρ = correctVar {τ} x ρ dρ
  correctness (app {σ} {τ} s t) ρ dρ =
    let
      f = ⟦ s ⟧ ρ
      g = ⟦ s ⟧ (update dρ)
      u = ⟦ t ⟧ ρ
      v = ⟦ t ⟧ (update dρ)
      Δf = ⟦ s ⟧Δ ρ dρ
      Δu = ⟦ t ⟧Δ ρ dρ
    in
      begin
        f u ⊞₍ τ ₎ call-change {σ} {τ} Δf u Δu
      ≡⟨  sym (is-valid {σ} {τ} Δf u Δu) ⟩
        (f ⊞₍ σ ⇒ τ ₎ Δf) (u ⊞₍ σ ₎ Δu)
      ≡⟨ correctness {σ ⇒ τ} s ρ dρ ⟨$⟩ correctness {σ} t ρ dρ ⟩
        g v
      ∎ where open ≡-Reasoning
  correctness {σ ⇒ τ} {Γ} (abs t) ρ dρ = ext (λ v →
    let
      -- dρ′ : ΔEnv (σ • Γ) (v • ρ)
      dρ′ = nil-change σ v • dρ
    in
      begin
        ⟦ t ⟧ (v • ρ) ⊞₍ τ ₎ ⟦ t ⟧Δ _ dρ′
      ≡⟨ correctness {τ} t _ dρ′ ⟩
        ⟦ t ⟧ (update dρ′)
      ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update dρ)) (v+[u-v]=u {σ}) ⟩
        ⟦ t ⟧ (v • update dρ)
      ∎
    ) where open ≡-Reasoning

  -- Corollary: (f ⊞ df) (v ⊞ dv) = f v ⊞ df v dv

  corollary : ∀ {σ τ Γ}
    (s : Term Γ (σ ⇒ τ)) (t : Term Γ σ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) →
      (⟦ s ⟧ ρ ⊞₍ σ ⇒ τ ₎ ⟦ s ⟧Δ ρ dρ)
        (⟦ t ⟧ ρ ⊞₍ σ ₎ ⟦ t ⟧Δ ρ dρ)
    ≡ (⟦ s ⟧ ρ) (⟦ t ⟧ ρ)
      ⊞₍ τ ₎
      (call-change {σ} {τ} (⟦ s ⟧Δ ρ dρ)) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)

  corollary {σ} {τ} s t ρ dρ =
    is-valid {σ} {τ} (⟦ s ⟧Δ ρ dρ) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)

  corollary-closed : ∀ {σ τ} (t : Term ∅ (σ ⇒ τ))
    (v : ⟦ σ ⟧) (dv : Change σ v)
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
