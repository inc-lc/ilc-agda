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

open import Popl14.Syntax.Term public

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
