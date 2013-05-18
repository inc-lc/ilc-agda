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

-- Δ-Context′: behaves like Δ-Context, but has an extra argument Γ′, a
-- prefix of its first argument which should not be touched.
Δ-Context′ : (Γ : Context) → Prefix Γ → Context
Δ-Context′ Γ ∅ = Δ-Context Γ
Δ-Context′ (.τ • Γ) (τ • Γ′) = τ • Δ-Context′ Γ Γ′

update′ : ∀ {Γ} → (Γ′ : Prefix Γ) → ⟦ Δ-Context′ Γ Γ′ ⟧ → ⟦ Γ ⟧
update′ ∅ ρ = update ρ
update′ (τ • Γ′) (v • ρ) = v • update′ Γ′ ρ

ignore′ : ∀ {Γ} → (Γ′ : Prefix Γ) → ⟦ Δ-Context′ Γ Γ′ ⟧ → ⟦ Γ ⟧
ignore′ ∅ ρ = ignore ρ
ignore′ (τ • Γ′) (v • ρ) = v • ignore′ Γ′ ρ

open import Relation.Binary.PropositionalEquality as P

Δ-Context-⋎ : ∀ Γ₁ Γ₂ →
  Δ-Context (Γ₁ ⋎ Γ₂) P.≡ Δ-Context Γ₁ ⋎ Δ-Context Γ₂
Δ-Context-⋎ ∅ Γ₂ = refl
Δ-Context-⋎ (τ • Γ₁) Γ₂ rewrite Δ-Context-⋎ Γ₁ Γ₂ = refl

Δ-Context-⋎-expanded : ∀ Γ₁ τ₂ Γ₂ →
  Δ-Context Γ₁ ⋎ (Δ-Type τ₂ • τ₂ • Δ-Context Γ₂) P.≡ Δ-Context (Γ₁ ⋎ (τ₂ • Γ₂))
Δ-Context-⋎-expanded Γ₁ τ₂ Γ₂ rewrite Δ-Context-⋎ Γ₁ (τ₂ • Γ₂) = refl

take-⋎-Δ-Context-drop-Δ-Context′ : ∀ Γ Γ′ →
  Δ-Context′ Γ Γ′ P.≡ take Γ Γ′ ⋎ Δ-Context (drop Γ Γ′)
take-⋎-Δ-Context-drop-Δ-Context′ ∅ ∅ = refl
take-⋎-Δ-Context-drop-Δ-Context′ (τ • Γ) ∅ = refl
take-⋎-Δ-Context-drop-Δ-Context′ (τ • Γ) (.τ • Γ′)
  rewrite take-⋎-Δ-Context-drop-Δ-Context′ Γ Γ′ = refl

-- WEAKENING

-- Weaken a term to a super context

{-
weaken : ∀ {Γ₁ Γ₂ Γ₃ τ} → Term (Γ₁ ⋎ Γ₃) τ → Term (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
weaken = {!!}

weaken : ∀ {Γ₁ Γ₂ Γ₃ τ} → Term (Γ₁ ⋎ Γ₃) τ → Term (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
weaken {Γ₁} {Γ₂} (abs  {τ₁ = τ} t) = abs (weaken {τ • Γ₁} {Γ₂} t)
weaken {Γ₁} {Γ₂} (app t₁ t₂) = app (weaken {Γ₁} {Γ₂} t₁) (weaken {Γ₁} {Γ₂} t₂)
weaken {Γ₁} {Γ₂} (var x) = var (lift {Γ₁} {Γ₂} x)
weaken {.(Δ-Type τ) • .τ • _} {Γ₂} (Δ {τ • Γ₃} t) = ?
--weaken {.(Δ-Type τ) • .τ • _} {Γ₂} (Δ {τ • Γ₃} t) = ?
--weaken {(Δ-Type τ) • τ • _} {Γ₂} (Δ {τ • Γ₃} t) = ?
--weaken {(Δ-Context .Γ₁)} {Γ₂} (Δ {Γ₁ ⋎ Γ₃} t) = ?
-}
