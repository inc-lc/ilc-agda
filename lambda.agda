module lambda where

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types public
open import Syntactic.Contexts Type public hiding (lift)

open Prefixes

open import Denotational.Notation
open import Denotational.Values public
open import Denotational.Environments Type ⟦_⟧Type public

-- TERMS

-- Syntax

data Term : Context → Type → Set where
  abs : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {Γ τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ

  true false : ∀ {Γ} → Term Γ bool
  if : ∀ {Γ τ} → (t₁ : Term Γ bool) (t₂ t₃ : Term Γ τ) → Term Γ τ

-- Denotational Semantics

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ app t₁ t₂ ⟧Term ρ = (⟦ t₁ ⟧Term ρ) (⟦ t₂ ⟧Term ρ)
⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ

⟦ true ⟧Term ρ = true
⟦ false ⟧Term ρ = false
⟦ if t₁ t₂ t₃ ⟧Term ρ with ⟦ t₁ ⟧Term ρ
... | true = ⟦ t₂ ⟧Term ρ
... | false = ⟦ t₃ ⟧Term ρ

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

-- NATURAL SEMANTICS

-- Syntax

data Env : Context → Set
data Val : Type → Set

data Val where
  ⟨abs_,_⟩ : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) (ρ : Env Γ) → Val (τ₁ ⇒ τ₂)
  true : Val bool
  false : Val bool

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
  if-true : ∀ {Γ τ} {ρ : Env Γ} {t₁ t₂ t₃} {v₂ : Val τ} →
    ρ ⊢ t₁ ↓ true →
    ρ ⊢ t₂ ↓ v₂ →
    ρ ⊢ if t₁ t₂ t₃ ↓ v₂
  if-false : ∀ {Γ τ} {ρ : Env Γ} {t₁ t₂ t₃} {v₃ : Val τ} →
    ρ ⊢ t₁ ↓ false →
    ρ ⊢ t₃ ↓ v₃ →
    ρ ⊢ if t₁ t₂ t₃ ↓ v₃

-- SOUNDNESS of natural semantics

⟦_⟧Env : ∀ {Γ} → Env Γ → ⟦ Γ ⟧
⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ ⟨abs t , ρ ⟩ ⟧Val = λ v → ⟦ t ⟧ (v • ⟦ ρ ⟧Env)
⟦ true ⟧Val = true
⟦ false ⟧Val = false

meaningOfEnv : ∀ {Γ} → Meaning (Env Γ)
meaningOfEnv = meaning ⟦_⟧Env

meaningOfVal : ∀ {τ} → Meaning (Val τ)
meaningOfVal = meaning ⟦_⟧Val

↦-sound : ∀ {Γ τ ρ v} {x : Var Γ τ} →
  ρ ⊢ x ↦ v →
  ⟦ x ⟧ ⟦ ρ ⟧ ≡ ⟦ v ⟧
↦-sound this = refl
↦-sound (that ↦) = ↦-sound ↦

↓-sound : ∀ {Γ τ ρ v} {t : Term Γ τ} →
  ρ ⊢ t ↓ v →
  ⟦ t ⟧ ⟦ ρ ⟧ ≡ ⟦ v ⟧
↓-sound abs = refl
↓-sound (app ↓₁ ↓₂ ↓′) = trans (cong₂ (λ x y → x y) (↓-sound ↓₁) (↓-sound ↓₂)) (↓-sound ↓′)
↓-sound (var ↦) = ↦-sound ↦
↓-sound (if-true ↓₁ ↓₂) rewrite ↓-sound ↓₁ = ↓-sound ↓₂
↓-sound (if-false ↓₁ ↓₃) rewrite ↓-sound ↓₁ = ↓-sound ↓₃

-- WEAKENING

-- Weaken a term to a super context

weaken : ∀ {Γ₁ Γ₂ Γ₃ τ} → Term (Γ₁ ⋎ Γ₃) τ → Term (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
weaken {Γ₁} {Γ₂} (abs  {τ₁ = τ} t) = abs (weaken {τ • Γ₁} {Γ₂} t)
weaken {Γ₁} {Γ₂} (app t₁ t₂) = app (weaken {Γ₁} {Γ₂} t₁) (weaken {Γ₁} {Γ₂} t₂)
weaken {Γ₁} {Γ₂} (var x) = var (lift {Γ₁} {Γ₂} x)
weaken {Γ₁} {Γ₂} true = true
weaken {Γ₁} {Γ₂} false = false
weaken {Γ₁} {Γ₂} (if e₁ e₂ e₃) = if (weaken {Γ₁} {Γ₂} e₁) (weaken {Γ₁} {Γ₂} e₂) (weaken {Γ₁} {Γ₂} e₃)
