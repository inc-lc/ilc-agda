module Syntax.Context.Popl14 where

-- Context specific to Popl14 version of the calculus
--
-- This module exports Syntax.Context specialized to
-- Syntax.Type.Popl14.Type and declares ΔContext appropriate
-- to Popl14 version of the incrementalization system.
-- This ΔContext may not make sense for other systems.

open import Syntax.Type.Popl14 public
import Syntax.Context Type as Ctx
open Ctx public hiding (lift)

ΔContext : Context → Context
ΔContext ∅ = ∅
ΔContext (τ • Γ) = ΔType τ • τ • ΔContext Γ

-- Aliasing of lemmas in Calculus Popl14

Γ≼Γ : ∀ {Γ} → Γ ≼ Γ
Γ≼Γ = ≼-refl

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ ΔContext Γ
Γ≼ΔΓ {∅} = ∅
Γ≼ΔΓ {τ • Γ} = drop ΔType τ • keep τ • Γ≼ΔΓ

-- Aliasing of weakening of variables

weakenVar : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Var Γ₁ τ → Var Γ₂ τ
weakenVar = Ctx.lift