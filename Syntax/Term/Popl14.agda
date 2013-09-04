module Syntax.Term.Popl14 where

-- Terms Calculus Popl14
--
-- Contents
-- - Term constructors
-- - Weakening on terms
-- - `fit`: weaken a term to its ΔContext
-- - diff-term, apply-term and their syntactic sugars

open import Syntax.Context.Popl14 public
open import Data.Integer

data Term (Γ : Context) : Type -> Set where
  intlit : (n : ℤ) → Term Γ int
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
weaken Γ₁≼Γ₂ (intlit x) = intlit x
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

fit : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) τ
fit = weaken Γ≼ΔΓ

diff-term  : ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ ΔType τ)
apply-term : ∀ {τ Γ} → Term Γ (ΔType τ ⇒ τ ⇒ τ)

-- Sugars for diff-term and apply-term
infixl 6 _⊕_ _⊝_
_⊕_ : ∀ {τ Γ} → Term Γ τ → Term Γ (ΔType τ) → Term Γ τ
_⊝_ : ∀ {τ Γ} → Term Γ τ → Term Γ τ → Term Γ (ΔType τ)
t ⊕ Δt = app (app apply-term Δt) t
s ⊝ t  = app (app  diff-term  s) t

apply-term {int} =
  let Δx = var (that this)
      x  = var this
  in abs (abs (add x Δx))
apply-term {bag} =
  let Δx = var (that this)
      x  = var this
  in abs (abs (union x Δx))
apply-term {σ ⇒ τ} =
  let
    Δf = var (that (that this))
    f  = var (that this)
    x  = var this
  in
  -- Δf   f    x
    abs (abs (abs
      (app f x ⊕ app (app Δf x) (x ⊝ x))))

diff-term {int} =
  let x = var (that this)
      y = var this
  in abs (abs (add x (minus y)))
diff-term {bag} =
  let x = var (that this)
      y = var this
  in abs (abs (union x (negate y)))
diff-term {σ ⇒ τ} =
  let
    g  = var (that (that (that this)))
    f  = var (that (that this))
    x  = var (that this)
    Δx = var this
  in
  -- g    f    x    Δx
    abs (abs (abs (abs
      (app g (x ⊕ Δx) ⊝ app f x))))
