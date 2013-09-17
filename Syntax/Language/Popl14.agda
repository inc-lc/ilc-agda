module Syntax.Language.Popl14 where

open import Popl14.Change.Term

open import Data.Integer

ΔConst : ∀ {Γ Σ τ} →
  Const Σ τ →
  Term Γ
    (internalizeContext
      (ΔContext′ Σ) (ΔType τ))

-- These helpers hide deBrujin indexes, providing an interface which is as
-- comfortable as HOAS. This should be generalized and moved to Parametric.Syntax.Term

ΔConst (intlit-const n) = intlit (+ 0)
ΔConst add-const = abs₄ (λ x Δx y Δy → add Δx Δy)
ΔConst minus-const = abs₂ (λ x Δx → minus Δx)
ΔConst empty-const = empty
ΔConst insert-const = abs₄ (λ x Δx y Δy → insert (x ⊕ Δx) (y ⊕ Δy) ⊝ insert x y)
ΔConst union-const = abs₄ (λ x Δx y Δy → union Δx Δy)
ΔConst negate-const = abs₂ (λ x Δx → negate Δx)
ΔConst flatmap-const = abs₄ (λ x Δx y Δy → flatmap (x ⊕ Δx) (y ⊕ Δy) ⊝ flatmap x y)
ΔConst sum-const = abs₂ (λ x Δx → sum Δx)
