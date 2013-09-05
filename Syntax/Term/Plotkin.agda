import Syntax.Type.Plotkin as Type
import Syntax.Context as Context

module Syntax.Term.Plotkin
    {B : Set {- of base types -}}
    {C : Context.Context {Type.Type B} → Type.Type B → Set {- of constants -}}
  where

-- Terms of languages described in Plotkin style

open import Function using (_∘_)
open import Data.Product

open Type B
open Context {Type}

open import Denotation.Environment Type
open import Syntax.Context.Plotkin B

data Term
  (Γ : Context) :
  (τ : Type) → Set

data Terms
  (Γ : Context) :
  (Σ : Context) → Set

data Term Γ where
  const : ∀ {Σ τ} →
    (c : C Σ τ) →
    Terms Γ Σ →
    Term Γ τ
  var : ∀ {τ} →
    (x : Var Γ τ) →
    Term Γ τ
  app : ∀ {σ τ}
    (s : Term Γ (σ ⇒ τ)) →
    (t : Term Γ σ) →
    Term Γ τ
  abs : ∀ {σ τ}
    (t : Term (σ • Γ) τ) →
    Term Γ (σ ⇒ τ)

data Terms Γ where
  ∅ : Terms Γ ∅
  _•_ : ∀ {τ Σ} →
    Term Γ τ →
    Terms Γ Σ →
    Terms Γ (τ • Σ)

infixr 9 _•_

-- g ⊝ f  = λ x . λ Δx . g (x ⊕ Δx) ⊝ f x
-- f ⊕ Δf = λ x . f x ⊕ Δf x (x ⊝ x)

lift-diff-apply : ∀ {Δbase : B → Type} →
  let
    Δtype = lift-Δtype Δbase
    term = Term
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

lift-diff : ∀ {Δbase : B → Type} →
  let
    Δtype = lift-Δtype Δbase
    term = Term
  in
  (∀ {ι Γ} → term Γ (base ι ⇒ base ι ⇒ Δtype (base ι))) →
  (∀ {ι Γ} → term Γ (Δtype (base ι) ⇒ base ι ⇒ base ι)) →
  ∀ {τ Γ} → term Γ (τ ⇒ τ ⇒ Δtype τ)

lift-diff diff apply = λ {τ Γ} →
  proj₁ (lift-diff-apply diff apply {τ} {Γ})

lift-apply : ∀ {Δbase : B → Type} →
  let
    Δtype = lift-Δtype Δbase
    term = Term
  in
  (∀ {ι Γ} → term Γ (base ι ⇒ base ι ⇒ Δtype (base ι))) →
  (∀ {ι Γ} → term Γ (Δtype (base ι) ⇒ base ι ⇒ base ι)) →
  ∀ {τ Γ} → term Γ (Δtype τ ⇒ τ ⇒ τ)

lift-apply diff apply = λ {τ Γ} →
  proj₂ (lift-diff-apply diff apply {τ} {Γ})

-- Weakening

weaken : ∀ {Γ₁ Γ₂ τ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Term Γ₁ τ →
  Term Γ₂ τ

weakenAll : ∀ {Γ₁ Γ₂ Σ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Terms Γ₁ Σ →
  Terms Γ₂ Σ

weaken Γ₁≼Γ₂ (const c ts) = const c (weakenAll Γ₁≼Γ₂ ts)
weaken Γ₁≼Γ₂ (var x) = var (lift Γ₁≼Γ₂ x)
weaken Γ₁≼Γ₂ (app s t) = app (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
weaken Γ₁≼Γ₂ (abs {σ} t) = abs (weaken (keep σ • Γ₁≼Γ₂) t)

weakenAll Γ₁≼Γ₂ ∅ = ∅
weakenAll Γ₁≼Γ₂ (t • ts) = weaken Γ₁≼Γ₂ t • weakenAll Γ₁≼Γ₂ ts

-- Specialized weakening
weaken₁ : ∀ {Γ σ τ} →
  Term Γ τ → Term (σ • Γ) τ
weaken₁ t = weaken (drop _ • ≼-refl) t

weaken₂ : ∀ {Γ α β τ} →
  Term Γ τ → Term (α • β • Γ) τ
weaken₂ t = weaken (drop _ • drop _ • ≼-refl) t

weaken₃ : ∀ {Γ α β γ τ} →
  Term Γ τ → Term (α • β • γ • Γ) τ
weaken₃ t = weaken (drop _ • drop _ • drop _ • ≼-refl) t

-- Shorthands for nested applications
app₂ : ∀ {Γ α β γ} →
    Term Γ (α ⇒ β ⇒ γ) →
    Term Γ α → Term Γ β → Term Γ γ
app₂ f x = app (app f x)

app₃ : ∀ {Γ α β γ δ} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ
app₃ f x = app₂ (app f x)

app₄ : ∀ {Γ α β γ δ ε} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε
app₄ f x = app₃ (app f x)

app₅ : ∀ {Γ α β γ δ ε ζ} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε ⇒ ζ) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε → Term Γ ζ
app₅ f x = app₄ (app f x)

app₆ : ∀ {Γ α β γ δ ε ζ η} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε ⇒ ζ ⇒ η) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε → Term Γ ζ → Term Γ η
app₆ f x = app₅ (app f x)

TermConstructor : (Γ Σ : Context) (τ : Type) → Set
TermConstructor Γ ∅ τ′ = Term Γ τ′
TermConstructor Γ (τ • Σ) τ′ = Term Γ τ → TermConstructor Γ Σ τ′

-- helper for lift-η-const, don't try to understand at home
lift-η-const-rec : ∀ {Σ Γ τ} → (Terms Γ Σ → Term Γ τ) → TermConstructor Γ Σ τ
lift-η-const-rec {∅} k = k ∅
lift-η-const-rec {τ • Σ} k = λ t → lift-η-const-rec (λ ts → k (t • ts))

lift-η-const : ∀ {Σ τ} → C Σ τ → ∀ {Γ} → TermConstructor Γ Σ τ
lift-η-const constant = lift-η-const-rec (const constant)
