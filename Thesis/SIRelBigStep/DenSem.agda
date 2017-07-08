module Thesis.SIRelBigStep.DenSem where

open import Data.Nat
open import Data.Product
open import Thesis.SIRelBigStep.Syntax

open import Data.Nat

⟦_⟧Type : Type → Set
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type
⟦ nat ⟧Type = ℕ
⟦ pair τ1 τ2 ⟧Type = ⟦ τ1 ⟧Type × ⟦ τ2 ⟧Type

import Base.Denotation.Environment
module Den = Base.Denotation.Environment Type ⟦_⟧Type
open import Base.Data.DependentList

⟦_⟧Const : ∀ {τ} → Const τ → ⟦ τ ⟧Type
⟦ lit n ⟧Const = n

⟦_⟧Primitive : ∀ {τ} → Primitive τ → ⟦ τ ⟧Type
⟦ succ ⟧Primitive = suc
⟦ add ⟧Primitive = λ { (n1 , n2) → n1 + n2}

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → Den.⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦_⟧SVal : ∀ {Γ τ} → SVal Γ τ → Den.⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ var x ⟧SVal ρ = Den.⟦ x ⟧Var ρ
⟦ abs t ⟧SVal ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ cons sv1 sv2 ⟧SVal ρ = ⟦ sv1 ⟧SVal ρ , ⟦ sv2 ⟧SVal ρ
⟦ const c ⟧SVal ρ = ⟦ c ⟧Const

⟦ val sv ⟧Term ρ = ⟦ sv ⟧SVal ρ
⟦ app s t ⟧Term ρ = ⟦ s ⟧SVal ρ (⟦ t ⟧SVal ρ)
⟦ lett s t ⟧Term ρ = ⟦ t ⟧Term ((⟦ s ⟧Term ρ) • ρ)
⟦ primapp vs vt ⟧Term ρ = ⟦ vs ⟧Primitive (⟦ vt ⟧SVal ρ)
