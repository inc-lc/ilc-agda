module Popl14.Change.Term where

-- Terms Calculus Popl14
--
-- Contents
-- - Term constructors
-- - Weakening on terms
-- - `fit`: weaken a term to its ΔContext
-- - diff-term, apply-term and their syntactic sugars

open import Data.Integer

open import Popl14.Syntax.Type public
open import Popl14.Syntax.Term public
open import Popl14.Change.Type public

import Parametric.Change.Term Const ΔBase as ChangeTerm

diff-base : ChangeTerm.DiffStructure
diff-base {base-int} = abs₂ (λ x y → add x (minus y))
diff-base {base-bag} = abs₂ (λ x y → union x (negate y))

apply-base : ChangeTerm.ApplyStructure
apply-base {base-int} = abs₂ (λ Δx x → add x Δx)
apply-base {base-bag} = abs₂ (λ Δx x → union x Δx)

diff-term  : ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ ΔType τ)
apply-term : ∀ {τ Γ} → Term Γ (ΔType τ ⇒ τ ⇒ τ)

-- Sugars for diff-term and apply-term
infixl 6 _⊕_ _⊝_
_⊕_ : ∀ {τ Γ} → Term Γ τ → Term Γ (ΔType τ) → Term Γ τ
_⊝_ : ∀ {τ Γ} → Term Γ τ → Term Γ τ → Term Γ (ΔType τ)
t ⊕ Δt = app (app apply-term Δt) t
s ⊝ t  = app (app  diff-term  s) t

apply-term {base ι} = apply-base {ι}
apply-term {σ ⇒ τ} =
    abs₃ (λ Δf f x →
      app f x ⊕ app (app Δf x) (x ⊝ x))

diff-term {base ι} = diff-base {ι}
diff-term {σ ⇒ τ} =
  abs₄ (λ g f x Δx →
    app g (x ⊕ Δx) ⊝ app f x)
