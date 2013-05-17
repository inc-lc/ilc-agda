module binding
    (Type : Set)
    (⟦_⟧Type : Type → Set)
  where

open import meaning

private
  meaningOfType : Meaning Type
  meaningOfType = meaning ⟦_⟧Type

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

⟦_⟧Context : Context → Set
⟦ ∅ ⟧Context = Empty
⟦ τ • Γ ⟧Context = Bind ⟦ τ ⟧ ⟦ Γ ⟧Context

meaningOfContext : Meaning Context
meaningOfContext = meaning ⟦_⟧Context

-- VARIABLES

-- Syntax

data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ

-- Denotational Semantics

⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ this ⟧Var (v • ρ) = v
⟦ that x ⟧Var (v • ρ) = ⟦ x ⟧Var ρ

meaningOfVar : ∀ {Γ τ} → Meaning (Var Γ τ)
meaningOfVar = meaning ⟦_⟧Var

-- WEAKENING

-- Prefix of a context

data Prefix : Context → Set where
  ∅ : ∀ {Γ} → Prefix Γ
  _•_ : ∀ {Γ} → (τ : Type) → Prefix Γ → Prefix (τ • Γ)

-- take only the prefix of a context

take : (Γ : Context) → Prefix Γ → Context
take Γ ∅ = ∅
take (τ • Γ) (.τ • Γ′) = τ • take Γ Γ′

-- drop the prefix of a context

drop : (Γ : Context) → Prefix Γ → Context
drop Γ ∅ = Γ
drop (τ • Γ) (.τ • Γ′) = drop Γ Γ′

-- Extend a context to a super context

infixr 10 _⋎_

_⋎_ : (Γ₁ Γ₂ : Context) → Context
∅ ⋎ Γ₂ = Γ₂
(τ • Γ₁) ⋎ Γ₂ = τ • Γ₁ ⋎ Γ₂

-- Lift a variable to a super context

lift : ∀ {Γ₁ Γ₂ Γ₃ τ} → Var (Γ₁ ⋎ Γ₃) τ → Var (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
lift {∅} {∅} x = x
lift {∅} {τ • Γ₂} x = that (lift {∅} {Γ₂} x)
lift {τ • Γ₁} {Γ₂} this = this
lift {τ • Γ₁} {Γ₂} (that x) = that (lift {Γ₁} {Γ₂} x)
