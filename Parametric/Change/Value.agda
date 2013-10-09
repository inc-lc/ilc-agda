import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value
import Parametric.Change.Type as ChangeType

module Parametric.Change.Value
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
    (ΔBase : ChangeType.Structure Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open ChangeType.Structure Base ΔBase

open import Base.Denotation.Notation

open import Data.Integer
open import Structure.Bag.Popl14

-- `diff` and `apply`, without validity proofs

ApplyStructure : Set
ApplyStructure = ∀ ι → ⟦ ι ⟧Base → ⟦ ΔBase ι ⟧Base → ⟦ ι ⟧Base

DiffStructure : Set
DiffStructure = ∀ ι → ⟦ ι ⟧Base → ⟦ ι ⟧Base → ⟦ ΔBase ι ⟧Base

module Structure
    (⟦apply-base⟧ : ApplyStructure)
    (⟦diff-base⟧ : DiffStructure)
  where

  ⟦apply⟧ : ∀ τ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
  ⟦diff⟧ : ∀ τ → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧

  infixl 6 ⟦apply⟧ ⟦diff⟧
  syntax ⟦apply⟧ τ v dv = v ⟦⊕₍ τ ₎⟧ dv
  syntax ⟦diff⟧ τ u v = u ⟦⊝₍ τ ₎⟧ v

  v ⟦⊕₍ base ι ₎⟧ Δv = ⟦apply-base⟧ ι v Δv
  f ⟦⊕₍ σ ⇒ τ ₎⟧ Δf = λ v → f v ⟦⊕₍ τ ₎⟧ Δf v (v ⟦⊝₍ σ ₎⟧ v)

  u ⟦⊝₍ base ι ₎⟧ v = ⟦diff-base⟧ ι u v
  g ⟦⊝₍ σ ⇒ τ ₎⟧ f = λ v Δv → (g (v ⟦⊕₍ σ ₎⟧ Δv)) ⟦⊝₍ τ ₎⟧ (f v)

  _⟦⊕⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
  _⟦⊕⟧_ {τ} = ⟦apply⟧ τ

  _⟦⊝⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧
  _⟦⊝⟧_ {τ} = ⟦diff⟧ τ

  alternate : ∀ {Γ} → ⟦ Γ ⟧ → ⟦ mapContext ΔType Γ ⟧ → ⟦ ΔContext Γ ⟧
  alternate {∅} ∅ ∅ = ∅
  alternate {τ • Γ} (v • ρ) (dv • dρ) = dv • v • alternate ρ dρ
