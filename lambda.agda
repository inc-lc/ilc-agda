module lambda where

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types public
open import Syntactic.Contexts Type public

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

weaken : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Term Γ₁ τ → Term Γ₂ τ
weaken ≼₁ (abs t) = abs (weaken (keep _ • ≼₁) t)
weaken ≼₁ (app t₁ t₂) = app (weaken ≼₁ t₁) (weaken ≼₁ t₂)
weaken ≼₁ (var x) = var (lift ≼₁ x)
weaken ≼₁ true = true
weaken ≼₁ false = false
weaken ≼₁ (if e₁ e₂ e₃) = if (weaken ≼₁ e₁) (weaken ≼₁ e₂) (weaken ≼₁ e₃)

-- SYMBOLIC EXECUTION
--
-- Naming Convention:
-- Γ ⟪_⟫X is like ⟦_⟧X but for symbolic execution in context Γ.

_⟪_⟫Type : Context → Type → Set
Γ₁ ⟪ τ₁ ⇒ τ₂ ⟫Type = ∀ {Γ₂} → Γ₁ ≼ Γ₂ → Γ₂ ⟪ τ₁ ⟫Type → Γ₂ ⟪ τ₂ ⟫Type
Γ₁ ⟪ bool ⟫Type = Term Γ₁ bool

module _ (Γ : Context) where
  import Denotational.Environments
  module SymEnv = Denotational.Environments Type (λ τ → Γ ⟪ τ ⟫Type)

  open SymEnv public using ()
    renaming (⟦_⟧Context to _⟪_⟫Context; ⟦_⟧Var to _⟪_⟫Var_)

liftVal : ∀ {τ Γ₁ Γ₂} → Γ₁ ≼ Γ₂ → Γ₁ ⟪ τ ⟫Type → Γ₂ ⟪ τ ⟫Type
liftVal {τ₁ ⇒ τ₂} ≼₁ v₁ = λ ≼₂ v₂ → v₁ (≼-trans ≼₁ ≼₂) v₂
liftVal {bool} ≼₁ v = weaken ≼₁ v

liftEnv : ∀ {Γ Γ₁ Γ₂} → Γ₁ ≼ Γ₂ → Γ₁ ⟪ Γ ⟫Context → Γ₂ ⟪ Γ ⟫Context
liftEnv {∅} ≼₁ ∅ = SymEnv.∅
liftEnv {τ • Γ} ≼₁ (v • ρ) = liftVal ≼₁ v SymEnv.• liftEnv ≼₁ ρ

mixed-if : ∀ {Γ₁} τ → (t₁ : Term Γ₁ bool) (v₂ v₃ : Γ₁ ⟪ τ ⟫Type) → Γ₁ ⟪ τ ⟫Type
mixed-if (τ₁ ⇒ τ₂) t₁ v₂ v₃ = λ ≼₁ v → mixed-if τ₂ (weaken ≼₁ t₁) (v₂ ≼₁ v) (v₃ ≼₁ v)
mixed-if bool t₁ t₂ t₃ = if t₁ t₂ t₃

_⟪_⟫Term_ : ∀ Γ₁ {Γ τ} → Term Γ τ → Γ₁ ⟪ Γ ⟫Context → Γ₁ ⟪ τ ⟫Type
Γ₁ ⟪ abs t ⟫Term ρ = λ {Γ₂} ≼₁ v → Γ₂ ⟪ t ⟫Term (v SymEnv.• liftEnv ≼₁ ρ)
Γ₁ ⟪ app t₁ t₂ ⟫Term ρ = (Γ₁ ⟪ t₁ ⟫Term ρ) ≼-refl (Γ₁ ⟪ t₂ ⟫Term ρ)
Γ₁ ⟪ var x ⟫Term ρ = Γ₁ ⟪ x ⟫Var ρ
Γ₁ ⟪ true ⟫Term ρ = true
Γ₁ ⟪ false ⟫Term ρ = false
Γ₁ ⟪ if t₁ t₂ t₃ ⟫Term ρ = mixed-if _ (Γ₁ ⟪ t₁ ⟫Term ρ) (Γ₁ ⟪ t₂ ⟫Term ρ) (Γ₁ ⟪ t₂ ⟫Term ρ)

↓ : ∀ {Γ} τ → Γ ⟪ τ ⟫Type → Term Γ τ
↑ : ∀ {Γ} τ → Term Γ τ → Γ ⟪ τ ⟫Type

↓ (τ₁ ⇒ τ₂) v = abs (↓ τ₂ (v (drop τ₁ • ≼-refl) (↑ τ₁ (var this))))
↓ bool v = v

↑ (τ₁ ⇒ τ₂) t = λ ≼₁ v → ↑ τ₂ (app (weaken ≼₁ t) (↓ τ₁ v))
↑ bool t = t

↑-Context : ∀ {Γ} → Γ ⟪ Γ ⟫Context
↑-Context {∅} = SymEnv.∅
↑-Context {τ • Γ} = ↑ τ (var this) SymEnv.• liftEnv (drop τ • ≼-refl) ↑-Context

norm : ∀ {Γ τ} → Term Γ τ → Term Γ τ
norm {Γ} {τ} t = ↓ τ (Γ ⟪ t ⟫Term ↑-Context)
