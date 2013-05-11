module incremental where

open import Relation.Binary.PropositionalEquality

-- SIMPLE TYPES

-- Syntax

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type

  -- `Δ τ` is the type of changes to `τ`
  Δ : (τ : Type) → Type

infixr 5 _⇒_

-- Denotational Semantics

Dom⟦_⟧ : Type -> Set
Dom⟦ τ₁ ⇒ τ₂ ⟧ = Dom⟦ τ₁ ⟧ → Dom⟦ τ₂ ⟧
Dom⟦ Δ τ ⟧ = Dom⟦ τ ⟧ → Dom⟦ τ ⟧

-- TYPING CONTEXTS, VARIABLES and WEAKENING

open import binding Type Dom⟦_⟧

-- TERMS

-- Syntax

data Term : Context → Type → Set where
  abs : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {Γ τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ

  -- `Δ x t` maps changes in `x` to changes in `t`
  Δ : ∀ {Γ τ₁ τ₂} → (x : Var Γ τ₁) → (t : Term Γ τ₂) → Term Γ (Δ τ₁ ⇒ Δ τ₂)

-- Denotational Semantics

eval⟦_⟧ : ∀ {Γ τ} → Term Γ τ → Env⟦ Γ ⟧ → Dom⟦ τ ⟧
eval⟦ abs t ⟧ ρ = λ v → eval⟦ t ⟧ (v • ρ)
eval⟦ app t₁ t₂ ⟧ ρ = (eval⟦ t₁ ⟧ ρ) (eval⟦ t₂ ⟧ ρ)
eval⟦ var x ⟧ ρ = lookup⟦ x ⟧ ρ
eval⟦ Δ x t ⟧ ρ = λ Δx _ → eval⟦ t ⟧ (update x Δx ρ)

-- NATURAL SEMANTICS

-- (without support for Δ for now)

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

-- SOUNDNESS of natural semantics

evalEnv⟦_⟧ : ∀ {Γ} → Env Γ → Env⟦ Γ ⟧
evalVal⟦_⟧ : ∀ {τ} → Val τ → Dom⟦ τ ⟧

evalEnv⟦ ∅ ⟧ = ∅
evalEnv⟦ v • ρ ⟧ = evalVal⟦ v ⟧ • evalEnv⟦ ρ ⟧

evalVal⟦ ⟨abs t , ρ ⟩ ⟧ = λ v → eval⟦ t ⟧ (v • evalEnv⟦ ρ ⟧)

↦-sound : ∀ {Γ τ ρ v} {x : Var Γ τ} →
  ρ ⊢ x ↦ v →
  lookup⟦ x ⟧ evalEnv⟦ ρ ⟧ ≡ evalVal⟦ v ⟧
↦-sound this = refl
↦-sound (that ↦) = ↦-sound ↦

↓-sound : ∀ {Γ τ ρ v} {t : Term Γ τ} →
  ρ ⊢ t ↓ v →
  eval⟦ t ⟧ evalEnv⟦ ρ ⟧ ≡ evalVal⟦ v ⟧
↓-sound abs = refl
↓-sound (app ↓₁ ↓₂ ↓′) = trans (cong₂ (λ x y → x y) (↓-sound ↓₁) (↓-sound ↓₂)) (↓-sound ↓′)
↓-sound (var ↦) = ↦-sound ↦

-- WEAKENING

-- Weaken a term to a super context

weaken : ∀ {Γ₁ Γ₂ Γ₃ τ} → Term (Γ₁ ⋎ Γ₃) τ → Term (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
weaken {Γ₁} {Γ₂} (abs  {τ₁ = τ} t) = abs (weaken {τ • Γ₁} {Γ₂} t)
weaken {Γ₁} {Γ₂} (app t₁ t₂) = app (weaken {Γ₁} {Γ₂} t₁) (weaken {Γ₁} {Γ₂} t₂)
weaken {Γ₁} {Γ₂} (var x) = var (lift {Γ₁} {Γ₂} x)
weaken {Γ₁} {Γ₂} (Δ x t) = Δ (lift {Γ₁} {Γ₂} x) (weaken {Γ₁} {Γ₂} t)