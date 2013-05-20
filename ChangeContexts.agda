module ChangeContexts where

-- CHANGE CONTEXTS
--
-- This module defines change contexts, that is, contexts where
-- for every value assertion x : τ, we also have a change
-- assertion ds : Δ-Type τ.

-- CHANGE ENVIRONMENTS
--
-- This module describes operations on change environments, that
-- is, environments where for every value binding x = ⟦ τ ⟧, we
-- also have a change assertion dx = ⟦ Δ-Type τ ⟧.

open import Syntactic.Types
open import Changes
open import Denotational.Values
open import Denotational.Notation

-- TYPING CONTEXTS, VARIABLES and WEAKENING

open import Syntactic.Contexts Type
open import Denotational.Environments Type ⟦_⟧Type

-- CHANGE CONTEXTS

Δ-Context : Context → Context
Δ-Context ∅ = ∅
Δ-Context (τ • Γ) = Δ-Type τ • τ • Δ-Context Γ

Changes : Context → Context
Changes ∅ = ∅
Changes (τ • Γ) = Δ-Type τ • Changes Γ

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
