module New.Lang where

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum

open import New.Types public
open import Base.Syntax.Context Type public
open import Base.Syntax.Vars Type public
open import Base.Data.DependentList public

module _ where
  data Const : (τ : Type) → Set where
     plus : Const (int ⇒ int ⇒ int)
     minus : Const (int ⇒ int ⇒ int)
     cons : ∀ {t1 t2} → Const (t1 ⇒ t2 ⇒ pair t1 t2)
     fst : ∀ {t1 t2} → Const (pair t1 t2 ⇒ t1)
     snd : ∀ {t1 t2} → Const (pair t1 t2 ⇒ t2)

  data Term (Γ : Context) :
    (τ : Type) → Set where
    -- constants aka. primitives
    const : ∀ {τ} →
      (c : Const τ) →
      Term Γ τ
    var : ∀ {τ} →
      (x : Var Γ τ) →
      Term Γ τ
    app : ∀ {σ τ}
      (s : Term Γ (σ ⇒ τ)) →
      (t : Term Γ σ) →
      Term Γ τ
    -- we use de Bruijn indicies, so we don't need binding occurrences.
    abs : ∀ {σ τ}
      (t : Term (σ • Γ) τ) →
      Term Γ (σ ⇒ τ)

  -- Weakening

  weaken : ∀ {Γ₁ Γ₂ τ} →
    (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
    Term Γ₁ τ →
    Term Γ₂ τ
  weaken Γ₁≼Γ₂ (const c) = const c
  weaken Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
  weaken Γ₁≼Γ₂ (app s t) = app (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
  weaken Γ₁≼Γ₂ (abs {σ} t) = abs (weaken (keep σ • Γ₁≼Γ₂) t)

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

open import Base.Denotation.Environment Type ⟦_⟧Type public

open import Data.Product
open import Data.Integer
⟦_⟧Const : ∀ {τ} → Const τ → ⟦ τ ⟧Type
⟦_⟧Const cons = λ v1 v2 → v1 , v2
⟦ plus ⟧Const = _+_
⟦ minus ⟧Const = _-_
⟦ fst ⟧Const (v1 , v2) = v1
⟦ snd ⟧Const (v1 , v2) = v2

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ const c ⟧Term ρ = ⟦ c ⟧Const
⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
⟦ app s t ⟧Term ρ = ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ)
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)

open import Theorem.CongApp
open import Postulate.Extensionality

weaken-sound : ∀ {Γ₁ Γ₂ τ} {Γ₁≼Γ₂ : Γ₁ ≼ Γ₂}
  (t : Term Γ₁ τ) (ρ : ⟦ Γ₂ ⟧Context) → ⟦ weaken Γ₁≼Γ₂ t ⟧Term ρ ≡ ⟦ t ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
weaken-sound {Γ₁≼Γ₂ = Γ₁≼Γ₂} (var x) ρ = weaken-var-sound Γ₁≼Γ₂ x ρ
weaken-sound (app s t) ρ = weaken-sound s ρ ⟨$⟩ weaken-sound t ρ
weaken-sound (abs t) ρ = ext (λ v → weaken-sound t (v • ρ))
weaken-sound (const c) ρ = refl
