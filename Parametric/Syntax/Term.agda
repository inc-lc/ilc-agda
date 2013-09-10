import Parametric.Syntax.Type as Type
import Base.Syntax.Context as Context

module Parametric.Syntax.Term
    {Base : Set}
    (C : Context.Context (Type.Type Base) → Type.Type Base → Set {- of constants -})
  where

-- Terms of languages described in Plotkin style

open import Function using (_∘_)
open import Data.Product

open Type Base
open Context Type

open import Syntax.Context.Plotkin Base

-- Declarations of Term and Terms to enable mutual recursion
data Term
  (Γ : Context) :
  (τ : Type) → Set

data Terms
  (Γ : Context) :
  (Σ : Context) → Set

-- (Term Γ τ) represents a term of type τ
-- with free variables bound in Γ.
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

-- (Terms Γ Σ) represents a list of terms with types from Σ
-- with free variables bound in Γ.
data Terms Γ where
  ∅ : Terms Γ ∅
  _•_ : ∀ {τ Σ} →
    Term Γ τ →
    Terms Γ Σ →
    Terms Γ (τ • Σ)

infixr 9 _•_

-- g ⊝ f  = λ x . λ Δx . g (x ⊕ Δx) ⊝ f x
-- f ⊕ Δf = λ x . f x ⊕ Δf x (x ⊝ x)

lift-diff-apply : ∀ {Δbase : Base → Type} →
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

lift-diff : ∀ {Δbase : Base → Type} →
  let
    Δtype = lift-Δtype Δbase
    term = Term
  in
  (∀ {ι Γ} → term Γ (base ι ⇒ base ι ⇒ Δtype (base ι))) →
  (∀ {ι Γ} → term Γ (Δtype (base ι) ⇒ base ι ⇒ base ι)) →
  ∀ {τ Γ} → term Γ (τ ⇒ τ ⇒ Δtype τ)

lift-diff diff apply = λ {τ Γ} →
  proj₁ (lift-diff-apply diff apply {τ} {Γ})

lift-apply : ∀ {Δbase : Base → Type} →
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

UncurriedTermConstructor : (Γ Σ : Context) (τ : Type) → Set
UncurriedTermConstructor Γ Σ τ = Terms Γ Σ → Term Γ τ

uncurriedConst : ∀ {Σ τ} → C Σ τ → ∀ {Γ} → UncurriedTermConstructor Γ Σ τ
uncurriedConst constant = const constant

CurriedTermConstructor : (Γ Σ : Context) (τ : Type) → Set
CurriedTermConstructor Γ ∅ τ′ = Term Γ τ′
CurriedTermConstructor Γ (τ • Σ) τ′ = Term Γ τ → CurriedTermConstructor Γ Σ τ′

curryTermConstructor : ∀ {Σ Γ τ} → UncurriedTermConstructor Γ Σ τ → CurriedTermConstructor Γ Σ τ
curryTermConstructor {∅} k = k ∅
curryTermConstructor {τ • Σ} k = λ t → curryTermConstructor (λ ts → k (t • ts))

curriedConst : ∀ {Σ τ} → C Σ τ → ∀ {Γ} → CurriedTermConstructor Γ Σ τ
curriedConst constant = curryTermConstructor (uncurriedConst constant)


-- HOAS-like smart constructors for lambdas, for different arities.

abs₁ :
  ∀ {Γ τ₁ τ} →
    (∀ {Γ′} → {Γ≼Γ′ : Γ ≼ Γ′} → (x : Term Γ′ τ₁) → Term Γ′ τ) →
    (Term Γ (τ₁ ⇒ τ))
abs₁ {Γ} {τ₁} =  λ f → abs (f {Γ≼Γ′ = drop τ₁ • ≼-refl} (var this))

abs₂ :
  ∀ {Γ τ₁ τ₂ τ} →
    (∀ {Γ′} → {Γ≼Γ′ : Γ ≼ Γ′} → Term Γ′ τ₁ → Term Γ′ τ₂ → Term Γ′ τ) →
    (Term Γ (τ₁ ⇒ τ₂ ⇒ τ))
abs₂ f =
  abs₁ (λ {_} {Γ≼Γ′} x₁ →
    abs₁ (λ {_} {Γ′≼Γ′₁} →
      f {Γ≼Γ′ = ≼-trans Γ≼Γ′ Γ′≼Γ′₁} (weaken Γ′≼Γ′₁ x₁)))

abs₃ :
  ∀ {Γ τ₁ τ₂ τ₃ τ} →
    (∀ {Γ′} → {Γ≼Γ′ : Γ ≼ Γ′} → Term Γ′ τ₁ → Term Γ′ τ₂ → Term Γ′ τ₃ → Term Γ′ τ) →
    (Term Γ (τ₁ ⇒ τ₂ ⇒ τ₃ ⇒ τ))
abs₃ f =
  abs₁ (λ {_} {Γ≼Γ′} x₁ →
    abs₂ (λ {_} {Γ′≼Γ′₁} →
      f {Γ≼Γ′ = ≼-trans Γ≼Γ′ Γ′≼Γ′₁} (weaken Γ′≼Γ′₁ x₁)))

abs₄ :
  ∀ {Γ τ₁ τ₂ τ₃ τ₄ τ} →
    (∀ {Γ′} → {Γ≼Γ′ : Γ ≼ Γ′} → Term Γ′ τ₁ → Term Γ′ τ₂ → Term Γ′ τ₃ → Term Γ′ τ₄ → Term Γ′ τ) →
    (Term Γ (τ₁ ⇒ τ₂ ⇒ τ₃ ⇒ τ₄ ⇒ τ))
abs₄ f =
  abs₁ (λ {_} {Γ≼Γ′} x₁ →
    abs₃ (λ {_} {Γ′≼Γ′₁} →
      f {Γ≼Γ′ = ≼-trans Γ≼Γ′ Γ′≼Γ′₁} (weaken Γ′≼Γ′₁ x₁)))

abs₅ :
  ∀ {Γ τ₁ τ₂ τ₃ τ₄ τ₅ τ} →
    (∀ {Γ′} → {Γ≼Γ′ : Γ ≼ Γ′} → Term Γ′ τ₁ → Term Γ′ τ₂ → Term Γ′ τ₃ → Term Γ′ τ₄ → Term Γ′ τ₅ → Term Γ′ τ) →
    (Term Γ (τ₁ ⇒ τ₂ ⇒ τ₃ ⇒ τ₄ ⇒ τ₅ ⇒ τ))
abs₅ f =
  abs₁ (λ {_} {Γ≼Γ′} x₁ →
    abs₄ (λ {_} {Γ′≼Γ′₁} →
      f {Γ≼Γ′ = ≼-trans Γ≼Γ′ Γ′≼Γ′₁} (weaken Γ′≼Γ′₁ x₁)))

abs₆ :
  ∀ {Γ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ} →
    (∀ {Γ′} → {Γ≼Γ′ : Γ ≼ Γ′} → Term Γ′ τ₁ → Term Γ′ τ₂ → Term Γ′ τ₃ → Term Γ′ τ₄ → Term Γ′ τ₅ → Term Γ′ τ₆ → Term Γ′ τ) →
    (Term Γ (τ₁ ⇒ τ₂ ⇒ τ₃ ⇒ τ₄ ⇒ τ₅ ⇒ τ₆ ⇒ τ))
abs₆ f =
  abs₁ (λ {_} {Γ≼Γ′} x₁ →
    abs₅ (λ {_} {Γ′≼Γ′₁} →
      f {Γ≼Γ′ = ≼-trans Γ≼Γ′ Γ′≼Γ′₁} (weaken Γ′≼Γ′₁ x₁)))
