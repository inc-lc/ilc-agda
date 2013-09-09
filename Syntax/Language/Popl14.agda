module Syntax.Language.Popl14 where

open import Syntax.Term.Popl14
open import Syntax.Context.Plotkin Popl14-type

open import Data.Integer

import Syntax.Language.Calculus as Calc

ΔConst : ∀ {Γ Σ τ} →
  Const Σ τ →
  Term Γ
    (internalizeContext
      (Calc.ΔContext′ ΔType Σ) (ΔType τ))

-- These helpers hide deBrujin indexes, providing an interface which is as
-- comfortable as HOAS. This should be generalized and moved to Syntax.Term.Plotkin

ΔConst (intlit-c n) = intlit (+ 0)
ΔConst add-c = abs₄ (λ x Δx y Δy → add Δx Δy)
ΔConst minus-c = abs₂ (λ x Δx → minus Δx)
ΔConst empty-c = empty
ΔConst insert-c = abs₄ (λ x Δx y Δy → insert (x ⊕ Δx) (y ⊕ Δy) ⊝ insert x y)
ΔConst union-c = abs₄ (λ x Δx y Δy → union Δx Δy)
ΔConst negate-c = abs₂ (λ x Δx → negate Δx)
ΔConst flatmap-c = abs₄ (λ x Δx y Δy → flatmap (x ⊕ Δx) (y ⊕ Δy) ⊝ flatmap x y)
ΔConst sum-c = abs₂ (λ x Δx → sum Δx)

Popl14 = Calc.calculus-with
  Popl14-type
  Const
  ΔType
  ΔConst
