module Syntax.Term.Popl14 where

-- Terms Calculus Popl14
--
-- Contents
-- - Term constructors
-- - Weakening on terms

open import Syntax.Context.Popl14 public
open import Data.Integer

data Term (Γ : Context) : Type -> Set where
  int : (n : ℤ) → Term Γ int
  add : (s : Term Γ int) (t : Term Γ int) → Term Γ int
  minus : (t : Term Γ int) → Term Γ int

  empty : Term Γ bag
  insert : (s : Term Γ int) (t : Term Γ bag) → Term Γ bag
  union : (s : Term Γ bag) → (t : Term Γ bag) → Term Γ bag
  negate : (t : Term Γ bag) → Term Γ bag

  flatmap : (s : Term Γ (int ⇒ bag)) (t : Term Γ bag) → Term Γ bag
  sum : (t : Term Γ bag) → Term Γ int

  var : ∀ {τ} → (x : Var Γ τ) → Term Γ τ
  app : ∀ {σ τ} → (s : Term Γ (σ ⇒ τ)) (t : Term Γ σ) → Term Γ τ
  abs : ∀ {σ τ} → (t : Term (σ • Γ) τ) → Term Γ (σ ⇒ τ)

weaken : ∀ {Γ₁ Γ₂ τ} → (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) → Term Γ₁ τ → Term Γ₂ τ
weaken Γ₁≼Γ₂ (int x) = int x
weaken Γ₁≼Γ₂ (add s t) = add (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
weaken Γ₁≼Γ₂ (minus t) = minus (weaken Γ₁≼Γ₂ t)

weaken Γ₁≼Γ₂ empty = empty
weaken Γ₁≼Γ₂ (insert s t) = insert (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
weaken Γ₁≼Γ₂ (union s t) = union (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
weaken Γ₁≼Γ₂ (negate t) = negate (weaken Γ₁≼Γ₂ t)

weaken Γ₁≼Γ₂ (flatmap s t) = flatmap (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
weaken Γ₁≼Γ₂ (sum t) = sum (weaken Γ₁≼Γ₂ t)

weaken Γ₁≼Γ₂ (var x) = var (weakenVar Γ₁≼Γ₂ x)
weaken Γ₁≼Γ₂ (app s t) = app (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
weaken Γ₁≼Γ₂ (abs {τ} t) = abs (weaken (keep τ • Γ₁≼Γ₂) t)
