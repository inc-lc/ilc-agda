module Thesis.SIRelBigStep.Syntax where

open import Data.Nat

open import Thesis.SIRelBigStep.Types public

data Const : (τ : Type) → Set where
  lit : ℕ → Const nat
  -- Adding this changes nothing without changes to the semantics.
  succ : Const (nat ⇒ nat)

data Term (Γ : Context) (τ : Type) : Set
-- Source values
data SVal (Γ : Context) : (τ : Type) → Set where
  var : ∀ {τ} →
    (x : Var Γ τ) →
    SVal Γ τ
  abs : ∀ {σ τ}
    (t : Term (σ • Γ) τ) →
    SVal Γ (σ ⇒ τ)
data Term (Γ : Context) (τ : Type) where
  val :
    SVal Γ τ →
    Term Γ τ
  -- constants aka. primitives
  const :
    (c : Const τ) →
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
