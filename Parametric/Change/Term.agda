import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Change.Type as ChangeType

module Parametric.Change.Term
    {Base : Set}
    (Constant : Term.Structure Base)
    (ΔBase : ChangeType.Structure Base)
  where

-- Terms that operate on changes

open Type.Structure Base
open Term.Structure Base Constant
open ChangeType.Structure Base ΔBase

open import Data.Product

DiffStructure : Set
DiffStructure = ∀ {ι Γ} → Term Γ (base ι ⇒ base ι ⇒ base (ΔBase ι))

ApplyStructure : Set
ApplyStructure = ∀ {ι Γ} → Term Γ (ΔType (base ι) ⇒ base ι ⇒ base ι)

module Structure
    (diff-base : DiffStructure)
    (apply-base : ApplyStructure)
  where

  -- g ⊝ f  = λ x . λ Δx . g (x ⊕ Δx) ⊝ f x
  -- f ⊕ Δf = λ x . f x ⊕ Δf x (x ⊝ x)

  lift-diff-apply :
    ∀ {τ Γ} →
      Term Γ (τ ⇒ τ ⇒ ΔType τ) × Term Γ (ΔType τ ⇒ τ ⇒ τ)

  lift-diff-apply {base ι} = diff-base , apply-base
  lift-diff-apply {σ ⇒ τ} =
    let
      -- syntactic sugars
      diffσ  = λ {Γ} → proj₁ (lift-diff-apply {σ} {Γ})
      diffτ  = λ {Γ} → proj₁ (lift-diff-apply {τ} {Γ})
      applyσ = λ {Γ} → proj₂ (lift-diff-apply {σ} {Γ})
      applyτ = λ {Γ} → proj₂ (lift-diff-apply {τ} {Γ})
      _⊝σ_ = λ {Γ} s t  → app₂ (diffσ {Γ}) s t
      _⊝τ_ = λ {Γ} s t  → app₂ (diffτ {Γ}) s t
      _⊕σ_ = λ {Γ} t Δt → app₂ (applyσ {Γ}) Δt t
      _⊕τ_ = λ {Γ} t Δt → app₂ (applyτ {Γ}) Δt t
    in
      abs₄ (λ g f x Δx → app f (x ⊕σ Δx) ⊝τ app g x)
      ,
      abs₃ (λ Δh h y → app h y ⊕τ app (app Δh y) (y ⊝σ y))

  diff-term :
    ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ ΔType τ)

  diff-term = λ {τ Γ} →
    proj₁ (lift-diff-apply {τ} {Γ})

  apply-term :
    ∀ {τ Γ} → Term Γ (ΔType τ ⇒ τ ⇒ τ)

  apply-term = λ {τ Γ} →
    proj₂ (lift-diff-apply {τ} {Γ})

  diff : ∀ {τ Γ} →
    Term Γ τ → Term Γ τ →
    Term Γ (ΔType τ)
  diff = app₂ diff-term

  apply : ∀ {τ Γ} →
    Term Γ (ΔType τ) → Term Γ τ →
    Term Γ τ
  apply = app₂ apply-term
