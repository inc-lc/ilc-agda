module ChangeContexts where

open import IlcModel
open import Changes
open import meaning
-- TYPING CONTEXTS, VARIABLES and WEAKENING

open import binding Type ⟦_⟧Type

-- CHANGE CONTEXTS

Δ-Context : Context → Context
Δ-Context ∅ = ∅
Δ-Context (τ • Γ) = Δ-Type τ • τ • Δ-Context Γ

update : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
update {∅} ∅ = ∅
update {τ • Γ} (dv • v • ρ) = apply dv v • update ρ

ignore : ∀ {Γ} → ⟦ Δ-Context Γ ⟧ → ⟦ Γ ⟧
ignore {∅} ∅ = ∅
ignore {τ • Γ} (dv • v • ρ) = v • ignore ρ

Δ-Context′ : (Γ : Context) → Prefix Γ → Context
Δ-Context′ Γ ∅ = Δ-Context Γ
Δ-Context′ (.τ • Γ) (τ • Γ′) = τ • Δ-Context′ Γ Γ′

update′ : ∀ {Γ} → (Γ′ : Prefix Γ) → ⟦ Δ-Context′ Γ Γ′ ⟧ → ⟦ Γ ⟧
update′ ∅ ρ = update ρ
update′ (τ • Γ′) (v • ρ) = v • update′ Γ′ ρ

ignore′ : ∀ {Γ} → (Γ′ : Prefix Γ) → ⟦ Δ-Context′ Γ Γ′ ⟧ → ⟦ Γ ⟧
ignore′ ∅ ρ = ignore ρ
ignore′ (τ • Γ′) (v • ρ) = v • ignore′ Γ′ ρ
