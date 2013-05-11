module binding
    (Type : Set)
    (Dom⟦_⟧ : Type → Set)
  where

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

-- OPERATIONS on environments

update : ∀ {Γ τ} → Var Γ τ → (Dom⟦ τ ⟧ → Dom⟦ τ ⟧) → Env⟦ Γ ⟧ → Env⟦ Γ ⟧
update this f (v • ρ) = f v • ρ
update (that x) f (v • ρ) = v • (update x f ρ)

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
