module Syntax.DeltaContext
    (Type : Set)
    (ΔType : Type → Type) where

-- Transform a context of values into a context of values and
-- changes.

open import Syntax.Context {Type}

ΔContext : Context → Context
ΔContext ∅ = ∅
ΔContext (τ • Γ) = ΔType τ • τ • ΔContext Γ
