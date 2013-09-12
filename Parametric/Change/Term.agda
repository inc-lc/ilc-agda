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

module Structure where

  -- g ⊝ f  = λ x . λ Δx . g (x ⊕ Δx) ⊝ f x
  -- f ⊕ Δf = λ x . f x ⊕ Δf x (x ⊝ x)

  lift-diff-apply :
    DiffStructure →
    (∀ {ι Γ} → Term Γ (base (ΔBase ι) ⇒ base ι ⇒ base ι)) →
    ∀ {τ Γ} →
      Term Γ (τ ⇒ τ ⇒ ΔType τ) × Term Γ (ΔType τ ⇒ τ ⇒ τ)

  lift-diff-apply diff apply {base ι} = diff , apply
  lift-diff-apply diff apply {σ ⇒ τ} =
    let
      -- for diff
      g  = var (that (that (that this)))
      f  = var (that (that this))
      x  = var (that this)
      Δx = var this
      -- for apply
      Δh = var (that (that this))
      h  = var (that this)
      y  = var this
      -- syntactic sugars
      diffσ  = λ {Γ} → proj₁ (lift-diff-apply diff apply {σ} {Γ})
      diffτ  = λ {Γ} → proj₁ (lift-diff-apply diff apply {τ} {Γ})
      applyσ = λ {Γ} → proj₂ (lift-diff-apply diff apply {σ} {Γ})
      applyτ = λ {Γ} → proj₂ (lift-diff-apply diff apply {τ} {Γ})
      _⊝σ_ = λ s t  → app (app diffσ s) t
      _⊝τ_ = λ s t  → app (app diffτ s) t
      _⊕σ_ = λ t Δt → app (app applyσ Δt) t
      _⊕τ_ = λ t Δt → app (app applyτ Δt) t
    in
      abs (abs (abs (abs (app f (x ⊕σ Δx) ⊝τ app g x))))
      ,
      abs (abs (abs (app h y ⊕τ app (app Δh y) (y ⊝σ y))))

  lift-diff :
    DiffStructure →
    (∀ {ι Γ} → Term Γ (base (ΔBase ι) ⇒ base ι ⇒ base ι)) →
    ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ ΔType τ)

  lift-diff diff apply = λ {τ Γ} →
    proj₁ (lift-diff-apply diff apply {τ} {Γ})

  lift-apply :
    DiffStructure →
    (∀ {ι Γ} → Term Γ (base (ΔBase ι) ⇒ base ι ⇒ base ι)) →
    ∀ {τ Γ} → Term Γ (ΔType τ ⇒ τ ⇒ τ)

  lift-apply diff apply = λ {τ Γ} →
    proj₂ (lift-diff-apply diff apply {τ} {Γ})
