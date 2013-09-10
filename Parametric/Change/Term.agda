import Parametric.Syntax.Type as Type
import Base.Syntax.Context as Context

module Parametric.Change.Term
    {Base : Set}
    (Constant : Context.Context (Type.Type Base) → Type.Type Base → Set {- of constants -})
    (Δbase : Base → Base)
  where

-- Terms that operate on changes

open Type Base
open Context Type

open import Parametric.Change.Type Δbase
open import Parametric.Syntax.Term Constant

open import Data.Product

-- g ⊝ f  = λ x . λ Δx . g (x ⊕ Δx) ⊝ f x
-- f ⊕ Δf = λ x . f x ⊕ Δf x (x ⊝ x)

lift-diff-apply :
  (∀ {ι Γ} → Term Γ (base ι ⇒ base ι ⇒ ΔType (base ι))) →
  (∀ {ι Γ} → Term Γ (ΔType (base ι) ⇒ base ι ⇒ base ι)) →
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
  (∀ {ι Γ} → Term Γ (base ι ⇒ base ι ⇒ ΔType (base ι))) →
  (∀ {ι Γ} → Term Γ (ΔType (base ι) ⇒ base ι ⇒ base ι)) →
  ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ ΔType τ)

lift-diff diff apply = λ {τ Γ} →
  proj₁ (lift-diff-apply diff apply {τ} {Γ})

lift-apply :
  (∀ {ι Γ} → Term Γ (base ι ⇒ base ι ⇒ ΔType (base ι))) →
  (∀ {ι Γ} → Term Γ (ΔType (base ι) ⇒ base ι ⇒ base ι)) →
  ∀ {τ Γ} → Term Γ (ΔType τ ⇒ τ ⇒ τ)

lift-apply diff apply = λ {τ Γ} →
  proj₂ (lift-diff-apply diff apply {τ} {Γ})
