------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Change contexts
--
-- This module specifies how a context of values is merged
-- together with the corresponding context of changes.
--
-- In the PLDI paper, instead of merging the contexts together, we just
-- concatenate them. For example, in the "typing rule" for Derive
-- in Sec. 3.2 of the paper, we write in the conclusion of the rule:
-- "Γ, ΔΓ ⊢ Derive(t) : Δτ". Simple concatenation is possible because
-- the paper uses named variables and assumes that no user variables
-- start with "d". In this formalization, we use de Bruijn indices, so
-- it is easier to alternate values and their changes in the context.
------------------------------------------------------------------------

module Base.Change.Context
    {Type : Set}
    (ΔType : Type → Type) where

open import Base.Syntax.Context Type

-- Transform a context of values into a context of values and
-- changes.
ΔContext : Context → Context
ΔContext ∅ = ∅
ΔContext (τ • Γ) = ΔType τ • τ • ΔContext Γ

-- like ΔContext, but ΔType τ and τ are swapped
ΔContext′ : Context → Context
ΔContext′ ∅ = ∅
ΔContext′ (τ • Γ) = τ • ΔType τ • ΔContext′ Γ

-- This sub-context relationship explains how to go back from
-- ΔContext Γ to Γ: You have to drop every other binding.
Γ≼ΔΓ : ∀ {Γ} → Γ ≼ ΔContext Γ
Γ≼ΔΓ {∅} = ∅
Γ≼ΔΓ {τ • Γ} = drop ΔType τ • keep τ • Γ≼ΔΓ
