module Syntactic.Terms.Total where

-- TERMS with a primitive for TOTAL DERIVATIVES
--
-- This module defines the syntax of terms that support a
-- primitive (Δ e) for computing the total derivative according
-- to all free variables in e and all future arguments of e if e
-- is a function.
--
-- Note that this is *not* the same as the ∂ operator in
-- definition/intro.tex. See discussion at:
--
--   https://github.com/ps-mr/ilc/pull/34#discussion_r4290325

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Changes
open import ChangeContexts

open import Relation.Binary.PropositionalEquality

-- TERMS

-- Syntax

data Term : Context → Type → Set where
  abs : ∀ {τ₁ τ₂ Γ} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
  app : ∀ {τ₁ τ₂ Γ} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
  var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ

  true false : ∀ {Γ} → Term Γ bool
  if : ∀ {Γ τ} → (t₁ : Term Γ bool) (t₂ t₃ : Term Γ τ) → Term Γ τ

  -- `Δ t` describes how t changes if its free variables or arguments change
  Δ : ∀ {Γ τ} → (t : Term Γ τ) → Term (Δ-Context Γ) (Δ-Type τ)
  weakenOne : ∀ Γ₁ τ₂ {Γ₃ τ} → Term (Γ₁ ⋎ Γ₃) τ → Term (Γ₁ ⋎ (τ₂ • Γ₃)) τ

substTerm : ∀ {τ Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Term Γ₁ τ → Term Γ₂ τ
substTerm {τ} {Γ₁} {Γ₂} ≡₁ t = subst (λ Γ → Term Γ τ) ≡₁ t
