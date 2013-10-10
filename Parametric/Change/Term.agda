import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Change.Type as ChangeType

module Parametric.Change.Term
    {Base : Set}
    (Const : Term.Structure Base)
    (ΔBase : ChangeType.Structure Base)
  where

-- Terms that operate on changes

open Type.Structure Base
open Term.Structure Base Const
open ChangeType.Structure Base ΔBase

open import Data.Product

DiffStructure : Set
DiffStructure = ∀ {ι Γ} → Term Γ (base ι ⇒ base ι ⇒ base (ΔBase ι))

ApplyStructure : Set
ApplyStructure = ∀ {ι Γ} → Term Γ (ΔType (base ι) ⇒ base ι ⇒ base ι)

module Structure
    (diff-base : DiffStructure)
    (apply-base : ApplyStructure)
  where

  -- g ⊝ f  = λ x . λ Δx . g (x ⊕ Δx) ⊝ f x
  -- f ⊕ Δf = λ x . f x ⊕ Δf x (x ⊝ x)

  diff-term : ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ ΔType τ)
  apply-term : ∀ {τ Γ} → Term Γ (ΔType τ ⇒ τ ⇒ τ)

  diff-term {base ι} = diff-base
  diff-term {σ ⇒ τ} =
    (let
       _⊝τ_ = λ {Γ} s t  → app₂ (diff-term {τ} {Γ}) s t
       _⊕σ_ = λ {Γ} t Δt → app₂ (apply-term {σ} {Γ}) Δt t
     in
       abs₄ (λ g f x Δx → app g (x ⊕σ Δx) ⊝τ app f x))

  apply-term {base ι} = apply-base
  apply-term {σ ⇒ τ} =
    (let
       _⊝σ_ = λ {Γ} s t  → app₂ (diff-term {σ} {Γ}) s t
       _⊕τ_ = λ {Γ} t Δt → app₂ (apply-term {τ} {Γ}) Δt t
     in
       abs₃ (λ Δh h y → app h y ⊕τ app (app Δh y) (y ⊝σ y)))

  diff : ∀ τ {Γ} →
    Term Γ τ → Term Γ τ →
    Term Γ (ΔType τ)
  diff _ = app₂ diff-term

  apply : ∀ τ {Γ} →
    Term Γ (ΔType τ) → Term Γ τ →
    Term Γ τ
  apply _ = app₂ apply-term

  infixl 6 apply diff
  syntax apply τ x Δx = Δx ⊕₍ τ ₎ x
  syntax diff τ x y = x ⊝₍ τ ₎ y

  infixl 6 _⊕_ _⊝_
  _⊝_ : ∀ {τ Γ} →
    Term Γ τ → Term Γ τ →
    Term Γ (ΔType τ)
  _⊝_ {τ} = diff τ

  _⊕_ : ∀ {τ Γ} →
    Term Γ (ΔType τ) → Term Γ τ →
    Term Γ τ
  _⊕_ {τ} = app₂ apply-term
