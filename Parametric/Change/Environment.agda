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

import Base.Data.DependentList as DependentList
open DependentList public using (∅; _•_)
open DependentList

open import Relation.Unary using (_⊆_)

ΔEnv-Entry : Type → Set
ΔEnv-Entry τ = Triple
  ⟦ τ ⟧
  (λ _ → ΔVal τ)
  (λ v dv → valid {τ} v dv)

ΔEnv : Context → Set
ΔEnv = DependentList ΔEnv-Entry

ignore-entry : ΔEnv-Entry ⊆ ⟦_⟧
ignore-entry (cons v _ _) = v

update-entry : ΔEnv-Entry ⊆ ⟦_⟧
update-entry {τ} (cons v dv R[v,dv]) = v ⊞₍ τ ₎ dv

ignore : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
ignore = map (λ {τ} → ignore-entry {τ})

update : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
update = map (λ {τ} → update-entry {τ})
