import Parametric.Syntax.Type as Type
import Parametric.Denotation.Value as Value
import Parametric.Change.Validity as Validity

module Parametric.Change.Environment
    {Base : Type.Structure}
    {⟦_⟧Base : Value.Structure Base}
    (validity-structure : Validity.Structure ⟦_⟧Base)
  where

open Type.Structure Base
open Value.Structure Base ⟦_⟧Base
open Validity.Structure ⟦_⟧Base validity-structure

open import Base.Denotation.Notation

import Structure.Tuples as Tuples
open Tuples public using (cons)
open Tuples

data EmptyEnv : Set where
  ∅ : EmptyEnv

ΔEnv : Context → Set

-- ΔEnv : Context → Set
ΔEnv ∅ = EmptyEnv
ΔEnv (τ • Γ) = Quadruple
  ⟦ τ ⟧
  (λ _ → ΔVal τ)
  (λ v dv → valid {τ} v dv)
  (λ _ _ _ → ΔEnv Γ)

ignore : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
ignore {∅} ρ = ∅
ignore {τ • Γ} (cons v dv R[v,dv] ρ) = v • ignore ρ

update : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
update {∅} ρ = ∅
update {τ • Γ} (cons v dv R[v,dv] ρ) = (v ⊞₍ τ ₎ dv) • update ρ
