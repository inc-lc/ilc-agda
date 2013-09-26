import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value

module Parametric.Denotation.Evaluation
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base

open import Base.Syntax.Context Type
open import Base.Denotation.Environment Type ⟦_⟧Type
open import Base.Denotation.Notation
open import Base.Data.DependentList

Structure : Set
Structure = ∀ {Σ τ} → Const Σ τ → ⟦ Σ ⟧ → ⟦ τ ⟧

module Structure (⟦_⟧Const : Structure) where
  ⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧

  ⟦_⟧Terms : ∀ {Γ Σ} → Terms Γ Σ → ⟦ Γ ⟧ → ⟦ Σ ⟧

  ⟦ const c args ⟧Term ρ = ⟦ c ⟧Const (⟦ args ⟧Terms ρ)
  ⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
  ⟦ app s t ⟧Term ρ = (⟦ s ⟧Term ρ) (⟦ t ⟧Term ρ)
  ⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)

  -- this is what we'd like to write.
  -- unfortunately termination checker complains.
  --
  --   ⟦ terms ⟧Terms ρ = map-IVT (λ t → ⟦ t ⟧Term ρ) terms
  --
  -- so we do explicit pattern matching instead.
  ⟦ ∅ ⟧Terms ρ = ∅
  ⟦ s • terms ⟧Terms ρ = ⟦ s ⟧Term ρ • ⟦ terms ⟧Terms ρ
  
  meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
  meaningOfTerm = meaning ⟦_⟧Term
