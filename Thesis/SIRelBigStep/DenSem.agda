module Thesis.SIRelBigStep.DenSem where

open import Data.Nat
open import Thesis.SIRelBigStep.Syntax

⟦_⟧Type : Type → Set
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type
⟦ nat ⟧Type = ℕ

import Base.Denotation.Environment
module Den = Base.Denotation.Environment Type ⟦_⟧Type
open import Base.Data.DependentList

⟦_⟧Const : ∀ {τ} → Const τ → ⟦ τ ⟧Type
⟦ lit n ⟧Const = n
⟦ succ ⟧Const = suc

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → Den.⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦_⟧SVal : ∀ {Γ τ} → SVal Γ τ → Den.⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ var x ⟧SVal ρ = Den.⟦ x ⟧Var ρ
⟦ abs t ⟧SVal ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ const c ⟧Term ρ = ⟦ c ⟧Const
⟦ val sv ⟧Term ρ = ⟦ sv ⟧SVal ρ
⟦ app s t ⟧Term ρ = ⟦ s ⟧SVal ρ (⟦ t ⟧SVal ρ)
⟦ lett s t ⟧Term ρ = ⟦ t ⟧Term ((⟦ s ⟧Term ρ) • ρ)
