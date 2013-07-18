module Syntax.Term.Plotkin where

-- Terms of languages described in Plotkin style

open import Syntax.Type.Plotkin
open import Syntax.Context

data Term
  {B : Set {- of base types -}}
  {C : Set {- of constants -}}
  {type-of : C → Type B}
  (Γ : Context {Type B}) :
  (τ : Type B) → Set
  where
  const : (c : C) → Term Γ (type-of c)
  var : ∀ {τ} → (x : Var Γ τ) → Term Γ τ
  app : ∀ {σ τ}
    (s : Term {B} {C} {type-of} Γ (σ ⇒ τ))
    (t : Term {B} {C} {type-of} Γ σ) → Term Γ τ
  abs : ∀ {σ τ}
    (t : Term {B} {C} {type-of} (σ • Γ) τ) → Term Γ (σ ⇒ τ)
