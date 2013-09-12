module Syntax.Context.Popl14 where

-- Context specific to Popl14 version of the calculus
--
-- This module exports Base.Syntax.Context specialized to
-- Syntax.Type.Popl14.Type and declares ΔContext appropriate
-- to Popl14 version of the incrementalization system.
-- This ΔContext may not make sense for other systems.

open import Popl14.Syntax.Type as Ctx public hiding (lift)
open import Popl14.Change.Type public

open import Base.Change.Context ΔType public

-- Aliasing of lemmas in Calculus Popl14

Γ≼Γ : ∀ {Γ} → Γ ≼ Γ
Γ≼Γ = ≼-refl

-- Aliasing of weakening of variables

weakenVar : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
weakenVar = Ctx.lift
