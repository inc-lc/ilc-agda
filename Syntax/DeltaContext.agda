module Syntax.DeltaContext
    {Type : Set}
    (ΔType : Type → Type) where

-- Transform a context of values into a context of values and
-- changes.

open import Syntax.Context {Type}

ΔContext : Context → Context
ΔContext ∅ = ∅
ΔContext (τ • Γ) = ΔType τ • τ • ΔContext Γ

-- like ΔContext, but ΔType τ and τ are swapped
ΔContext′ : Context → Context
ΔContext′ ∅ = ∅
ΔContext′ (τ • Γ) = τ • ΔType τ • ΔContext′ Γ

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ ΔContext Γ
Γ≼ΔΓ {∅} = ∅
Γ≼ΔΓ {τ • Γ} = drop ΔType τ • keep τ • Γ≼ΔΓ
