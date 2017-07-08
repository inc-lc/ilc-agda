module Thesis.SIRelBigStep.Syntax where

open import Data.Nat

open import Thesis.SIRelBigStep.Types public

data Primitive : (τ : Type) → Set where
  succ : Primitive (nat ⇒ nat)
  add : Primitive (pair nat nat ⇒ nat)

data Const : (τ : Type) → Set where
  lit : (n : ℕ) → Const nat

data Term (Γ : Context) (τ : Type) : Set
-- Source values
data SVal (Γ : Context) : (τ : Type) → Set where
  var : ∀ {τ} →
    (x : Var Γ τ) →
    SVal Γ τ
  abs : ∀ {σ τ}
    (t : Term (σ • Γ) τ) →
    SVal Γ (σ ⇒ τ)
  cons : ∀ {τ1 τ2}
    (sv1 : SVal Γ τ1)
    (sv2 : SVal Γ τ2) →
    SVal Γ (pair τ1 τ2)
  const : ∀ {τ} → (c : Const τ) → SVal Γ τ

data Term (Γ : Context) (τ : Type) where
  val :
    SVal Γ τ →
    Term Γ τ
  primapp : ∀ {σ}
    (p : Primitive (σ ⇒ τ)) →
    (sv : SVal Γ σ) →
    Term Γ τ
  -- we use de Bruijn indices, so we don't need binding occurrences.
  app : ∀ {σ}
    (vs : SVal Γ (σ ⇒ τ)) →
    (vt : SVal Γ σ) →
    Term Γ τ
  lett : ∀ {σ}
    (s : Term Γ σ) →
    (t : Term (σ • Γ) τ) →
    Term Γ τ
