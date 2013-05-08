module incremental where

-- SIMPLE TYPES

-- Syntax

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type

infixr 5 _⇒_

-- Denotational Semantics

Dom⟦_⟧ : Type -> Set
Dom⟦ τ₁ ⇒ τ₂ ⟧ = Dom⟦ τ₁ ⟧ → Dom⟦ τ₂ ⟧

-- TYPING CONTEXTS

-- Syntax

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

infixr 9 _•_

-- Denotational Semantics

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

-- Denotational Semantics

lookup⟦_⟧ : ∀ {Γ τ} → Var Γ τ → Env⟦ Γ ⟧ → Dom⟦ τ ⟧
lookup⟦ this ⟧ (v • ρ) = v
lookup⟦ that x ⟧ (v • ρ) = lookup⟦ x ⟧ ρ

-- TERMS

-- Syntax

data Term : Context → Type → Set where
  abs : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {Γ τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ

-- Denotational Semantics

eval⟦_⟧ : ∀ {Γ τ} → Term Γ τ → Env⟦ Γ ⟧ → Dom⟦ τ ⟧
eval⟦ abs t ⟧ ρ = λ v → eval⟦ t ⟧ (v • ρ)
eval⟦ app t₁ t₂ ⟧ ρ = (eval⟦ t₁ ⟧ ρ) (eval⟦ t₂ ⟧ ρ)
eval⟦ var x ⟧ ρ = lookup⟦ x ⟧ ρ

-- NATURAL SEMANTICS

-- Syntax

data Env : Context → Set
data Val : Type → Set

data Val where
  ⟨abs_,_⟩ : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) (ρ : Env Γ) → Val (τ₁ ⇒ τ₂)

data Env where
  ∅ : Env ∅
  _•_ : ∀ {Γ τ} → Val τ → Env Γ → Env (τ • Γ)

-- Lookup

infixr 8 _⊢_↓_ _⊢_↦_

data _⊢_↦_ : ∀ {Γ τ} → Env Γ → Var Γ τ → Val τ → Set where
  this : ∀ {Γ τ} {ρ : Env Γ} {v : Val τ} →
    v • ρ ⊢ this ↦ v
  that : ∀ {Γ τ₁ τ₂ x} {ρ : Env Γ} {v₁ : Val τ₁} {v₂ : Val τ₂} →
    ρ ⊢ x ↦ v₂ →
    v₁ • ρ ⊢ that x ↦ v₂

-- Reduction

data _⊢_↓_ : ∀ {Γ τ} → Env Γ → Term Γ τ → Val τ → Set where
  abs : ∀ {Γ τ₁ τ₂ ρ} {t : Term (τ₁ • Γ) τ₂} →
    ρ ⊢ abs t ↓ ⟨abs t , ρ ⟩
  app : ∀ {Γ Γ′ τ₁ τ₂ ρ ρ′ v₂ v′} {t₁ : Term Γ (τ₁ ⇒ τ₂)} {t₂ : Term Γ τ₁} {t′ : Term (τ₁ • Γ′) τ₂} →
    ρ ⊢ t₁ ↓ ⟨abs t′ , ρ′ ⟩ →
    ρ ⊢ t₂ ↓ v₂ →
    v₂ • ρ′ ⊢ t′ ↓ v′ →
    ρ ⊢ app t₁ t₂ ↓ v′
  var : ∀ {Γ τ x} {ρ : Env Γ} {v : Val τ}→
    ρ ⊢ x ↦ v →
    ρ ⊢ var x ↓ v

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

-- CHANGE VARIABLES

-- changes 'x' to 'dx'

rename : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
rename this = that this
rename (that x) = that (that (rename x))

-- changes 'x' to 'nil' (if internally bound) or 'dx' (if externally bound)

Δ-var : ∀ {Γ₁ Γ₂ τ} → Var (Γ₁ ⋎ Γ₂) τ → Term (Δ-Context Γ₂) (Δ-Type τ)
Δ-var {∅} x = var (rename x)
Δ-var {τ • Γ} this = nil
Δ-var {τ • Γ} (that x) = Δ-var {Γ} x

-- CHANGE TERMS

Δ-term : ∀ {Γ₁ Γ₂ τ} → Term (Γ₁ ⋎ Γ₂) τ → Term (Γ₁ ⋎ Δ-Context Γ₂) (Δ-Type τ)
Δ-term {Γ} (abs {τ₁ = τ} t) = abs (Δ-term {τ • Γ} t)
Δ-term {Γ} (app t₁ t₂) = {!!}
Δ-term {Γ} (var x) = weaken {∅} {Γ} (Δ-var {Γ} x)
