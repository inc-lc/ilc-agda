module incremental where

-- SIMPLE TYPES

-- Syntax

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type

infixr 5 _⇒_

-- Semantics

Dom⟦_⟧ : Type -> Set
Dom⟦ τ₁ ⇒ τ₂ ⟧ = Dom⟦ τ₁ ⟧ → Dom⟦ τ₂ ⟧

-- TYPING CONTEXTS

-- Syntax

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

infixr 9 _•_

-- Semantics

data Empty : Set where
  ∅ : Empty

data Bind A B : Set where
  _•_ : (v : A) (ρ : B) → Bind A B

Env⟦_⟧ : Context → Set
Env⟦ ∅ ⟧ = Empty
Env⟦ τ • Γ ⟧ = Bind Dom⟦ τ ⟧ Env⟦ Γ ⟧

-- VARIABLES

-- Syntax

data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ

-- Semantics

lookup⟦_⟧ : ∀ {Γ τ} → Var Γ τ → Env⟦ Γ ⟧ → Dom⟦ τ ⟧
lookup⟦ this ⟧ (v • ρ) = v
lookup⟦ that x ⟧ (v • ρ) = lookup⟦ x ⟧ ρ

-- TERMS

-- Syntax

data Term : Context → Type → Set where
  abs : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {Γ τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ

-- Semantics

eval⟦_⟧ : ∀ {Γ τ} → Term Γ τ → Env⟦ Γ ⟧ → Dom⟦ τ ⟧
eval⟦ abs t ⟧ ρ = λ v → eval⟦ t ⟧ (v • ρ)
eval⟦ app t₁ t₂ ⟧ ρ = (eval⟦ t₁ ⟧ ρ) (eval⟦ t₂ ⟧ ρ)
eval⟦ var x ⟧ ρ = lookup⟦ x ⟧ ρ


-- WEAKENING

-- Extend a context to a super context

infixr 10 _⋎_

_⋎_ : (Γ₁ Γ₁ : Context) → Context
∅ ⋎ Γ₂ = Γ₂
(τ • Γ₁) ⋎ Γ₂ = τ • Γ₁ ⋎ Γ₂

-- Lift a variable to a super context

lift : ∀ {Γ₁ Γ₂ Γ₃ τ} → Var (Γ₁ ⋎ Γ₃) τ → Var (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
lift {∅} {∅} x = x
lift {∅} {τ • Γ₂} x = that (lift {∅} {Γ₂} x)
lift {τ • Γ₁} {Γ₂} this = this
lift {τ • Γ₁} {Γ₂} (that x) = that (lift {Γ₁} {Γ₂} x)

-- Weaken a term to a super context

weaken : ∀ {Γ₁ Γ₂ Γ₃ τ} → Term (Γ₁ ⋎ Γ₃) τ → Term (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
weaken {Γ₁} {Γ₂} (abs  {τ₁ = τ} t) = abs (weaken {τ • Γ₁} {Γ₂} t)
weaken {Γ₁} {Γ₂} (app t₁ t₂) = app (weaken {Γ₁} {Γ₂} t₁) (weaken {Γ₁} {Γ₂} t₂)
weaken {Γ₁} {Γ₂} (var x) = var (lift {Γ₁} {Γ₂} x)

-- CHANGE TYPES

Δ-Type : Type → Type
Δ-Type (τ₁ ⇒ τ₂) = τ₁ ⇒ Δ-Type τ₂

apply : ∀ {τ Γ} → Term Γ (Δ-Type τ ⇒ τ ⇒ τ)
apply {τ₁ ⇒ τ₂} =
    abs (abs (abs (app (app apply (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))
 -- λdf. λf.  λx.           apply (     df                       x        )  (     f                 x        )

compose : ∀ {τ Γ} → Term Γ (Δ-Type τ ⇒ Δ-Type τ ⇒ Δ-Type τ)
compose {τ₁ ⇒ τ₂} =
    abs (abs (abs (app (app compose (app (var (that (that this))) (var this))) (app (var (that this)) (var this)))))
 -- λdf. λdg. λx.           compose (     df                       x         ) (     dg                x      )

nil : ∀ {τ Γ} → Term Γ (Δ-Type τ)
nil {τ₁ ⇒ τ₂} =
    abs nil
 -- λx. nil

-- Hey, apply is α-equivalent to compose, what's going on?
-- Oh, and `Δ-Type` is the identity function?

-- CHANGE CONTEXTS

Δ-Context : Context → Context
Δ-Context ∅ = ∅
Δ-Context (τ • Γ) = τ • Δ-Type τ • Δ-Context Γ

-- CHANGING TERMS WHEN THE ENVIRONMENT CHANGES

Δ-term : ∀ {Γ₁ Γ₂ τ} → Term (Γ₁ ⋎ Γ₂) τ → Term (Γ₁ ⋎ Δ-Context Γ₂) (Δ-Type τ)
Δ-term {Γ} (abs {τ₁ = τ} t) = abs (Δ-term {τ • Γ} t)
Δ-term {Γ} (app t₁ t₂) = {!!}
Δ-term {Γ} (var x) = {!!}
