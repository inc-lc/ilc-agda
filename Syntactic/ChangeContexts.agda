module Syntactic.ChangeContexts where

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
open import Syntactic.ChangeTypes.ChangesAreDerivatives

open import Denotational.Notation
open import Denotational.Values

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
