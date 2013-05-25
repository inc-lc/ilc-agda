module ChangeContexts where

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.ChangeTypes.ChangesAreDerivatives
open import Syntactic.ChangeContexts

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Changes

-- CHANGE CONTEXTS
-- Properties

≼-Δ-Context : ∀ {Γ} → Γ ≼ Δ-Context Γ
≼-Δ-Context {∅} = ∅
≼-Δ-Context {τ • Γ} = drop (Δ-Type τ) • keep τ • ≼-Δ-Context

≼-Changes : ∀ {Γ} → Changes Γ ≼ Δ-Context Γ
≼-Changes {∅} = ∅
≼-Changes {τ • Γ} = keep Δ-Type τ • drop τ • ≼-Changes

-- OPERATIONS on CHANGE ENVIRONMENTS

update : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
update {∅} ∅ = ∅
update {τ • Γ} (dv • v • ρ) = apply dv v • update ρ

ignore : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
ignore = ⟦ ≼-Δ-Context ⟧
