module Denotational.Closures where

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Closures

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total

⟦_⟧Env : ∀ {Γ} → Env Γ → ⟦ Γ ⟧
⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ ⟨abs t , ρ ⟩ ⟧Val = λ v → ⟦ t ⟧ (v • ⟦ ρ ⟧Env)
⟦ vtrue ⟧Val = true
⟦ vfalse ⟧Val = false

meaningOfEnv : ∀ {Γ} → Meaning (Env Γ)
meaningOfEnv = meaning ⟦_⟧Env

meaningOfVal : ∀ {τ} → Meaning (Val τ)
meaningOfVal = meaning ⟦_⟧Val
