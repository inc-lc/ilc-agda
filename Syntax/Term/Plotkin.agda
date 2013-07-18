module Syntax.Term.Plotkin where

-- Terms of languages described in Plotkin style

open import Function using (_∘_)
open import Data.Product
open import Syntax.Type.Plotkin
open import Syntax.Context

data Term
  {B : Set {- of base types -}}
  {C : Set {- of constants -}}
  {type-of : C → Type B}
  (Γ : Context {Type B}) :
  (τ : Type B) → Set
  where
  const : (c : C) → Term Γ (type-of c)
  var : ∀ {τ} → (x : Var Γ τ) → Term Γ τ
  app : ∀ {σ τ}
    (s : Term {B} {C} {type-of} Γ (σ ⇒ τ))
    (t : Term {B} {C} {type-of} Γ σ) → Term Γ τ
  abs : ∀ {σ τ}
    (t : Term {B} {C} {type-of} (σ • Γ) τ) → Term Γ (σ ⇒ τ)

-- g ⊝ f  = λ x . λ Δx . g (x ⊕ Δx) ⊝ f x
-- f ⊕ Δf = λ x . f x ⊕ Δf x (x ⊝ x)

lift-diff-apply : ∀ {B C type-of} {Δbase : B → Type B} →
  let
    Δtype = lift-Δtype Δbase
    term = Term {B} {C} {type-of}
  in
  (∀ {ι Γ} → term Γ (base ι ⇒ base ι ⇒ Δtype (base ι))) →
  (∀ {ι Γ} → term Γ (Δtype (base ι) ⇒ base ι ⇒ base ι)) →
  ∀ {τ Γ} →
    term Γ (τ ⇒ τ ⇒ Δtype τ) × term Γ (Δtype τ ⇒ τ ⇒ τ)

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

lift-diff : ∀ {B C type-of} {Δbase : B → Type B} →
  let
    Δtype = lift-Δtype Δbase
    term = Term {B} {C} {type-of}
  in
  (∀ {ι Γ} → term Γ (base ι ⇒ base ι ⇒ Δtype (base ι))) →
  (∀ {ι Γ} → term Γ (Δtype (base ι) ⇒ base ι ⇒ base ι)) →
  ∀ {τ Γ} → term Γ (τ ⇒ τ ⇒ Δtype τ)

lift-diff diff apply = λ {τ Γ} →
  proj₁ (lift-diff-apply diff apply {τ} {Γ})

lift-apply : ∀ {B C type-of} {Δbase : B → Type B} →
  let
    Δtype = lift-Δtype Δbase
    term = Term {B} {C} {type-of}
  in
  (∀ {ι Γ} → term Γ (base ι ⇒ base ι ⇒ Δtype (base ι))) →
  (∀ {ι Γ} → term Γ (Δtype (base ι) ⇒ base ι ⇒ base ι)) →
  ∀ {τ Γ} → term Γ (Δtype τ ⇒ τ ⇒ τ)

lift-apply diff apply = λ {τ Γ} →
  proj₂ (lift-diff-apply diff apply {τ} {Γ})

-- Weakening

weaken : ∀ {B C ⊢ Γ₁ Γ₂ τ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Term {B} {C} {⊢} Γ₁ τ →
  Term {B} {C} {⊢} Γ₂ τ
weaken Γ₁≼Γ₂ (const c) = const c
weaken Γ₁≼Γ₂ (var x) = var (lift Γ₁≼Γ₂ x)
weaken Γ₁≼Γ₂ (app s t) = app (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
weaken Γ₁≼Γ₂ (abs {σ} t) = abs (weaken (keep σ • Γ₁≼Γ₂) t)

-- Specialized weakening
weaken₁ : ∀ {B C ⊢ Γ σ τ} →
  Term {B} {C} {⊢} Γ τ → Term {B} {C} {⊢} (σ • Γ) τ
weaken₁ t = weaken (drop _ • ≼-refl) t

weaken₂ : ∀ {B C ⊢ Γ α β τ} →
  Term {B} {C} {⊢} Γ τ → Term {B} {C} {⊢} (α • β • Γ) τ
weaken₂ t = weaken (drop _ • drop _ • ≼-refl) t

weaken₃ : ∀ {B C ⊢ Γ α β γ τ} →
  Term {B} {C} {⊢} Γ τ → Term {B} {C} {⊢} (α • β • γ • Γ) τ
weaken₃ t = weaken (drop _ • drop _ • drop _ • ≼-refl) t
