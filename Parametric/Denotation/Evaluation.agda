------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Standard evaluation (Def. 3.3 and Fig. 4i)
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value

module Parametric.Denotation.Evaluation
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base

open import Base.Denotation.Notation

open import Base.Data.DependentList
open import Relation.Binary.PropositionalEquality
open import Theorem.CongApp
open import Postulate.Extensionality

-- Extension Point: Evaluation of constants.
Structure : Set
Structure = ∀ {τ} → Const τ → ⟦ τ ⟧

module Structure (⟦_⟧Const : Structure) where
  ⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧

  -- We provide: Evaluation of arbitrary terms.
  ⟦ const c ⟧Term ρ = ⟦ c ⟧Const
  ⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
  ⟦ app s t ⟧Term ρ = (⟦ s ⟧Term ρ) (⟦ t ⟧Term ρ)
  ⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)

  instance
    meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
    meaningOfTerm = meaning ⟦_⟧Term

  weaken-sound : ∀ {Γ₁ Γ₂ τ} {Γ₁≼Γ₂ : Γ₁ ≼ Γ₂}
    (t : Term Γ₁ τ) (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken Γ₁≼Γ₂ t ⟧ ρ ≡ ⟦ t ⟧ (⟦ Γ₁≼Γ₂ ⟧ ρ)
  weaken-sound {Γ₁≼Γ₂ = Γ₁≼Γ₂} (var x) ρ = weaken-var-sound Γ₁≼Γ₂ x ρ
  weaken-sound (app s t) ρ = weaken-sound s ρ ⟨$⟩ weaken-sound t ρ
  weaken-sound (abs t) ρ = ext (λ v → weaken-sound t (v • ρ))
  weaken-sound (const c) ρ = refl
