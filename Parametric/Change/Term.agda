------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Terms that operate on changes (Fig. 3).
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Change.Type as ChangeType

module Parametric.Change.Term
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (ΔBase : ChangeType.Structure Base)
  where

-- Terms that operate on changes

open Type.Structure Base
open Term.Structure Base Const
open ChangeType.Structure Base ΔBase

open import Data.Product

-- Extension point 1: A term for ⊝ on base types.
DiffStructure : Set
DiffStructure = ∀ {ι Γ} → Term Γ (base ι ⇒ base ι ⇒ ΔBase ι)

-- Extension point 2: A term for ⊕ on base types.
ApplyStructure : Set
ApplyStructure = ∀ {ι Γ} → Term Γ (ΔType (base ι) ⇒ base ι ⇒ base ι)

-- Extension point 3: A term for 0 on base types.
NilStructure : Set
NilStructure = ∀ {ι Γ} → Term Γ (base ι ⇒ ΔBase ι)

module Structure
    (apply-base : ApplyStructure)
    (diff-base  : DiffStructure)
    (nil-base   : NilStructure)
  where

  -- g ⊝ f  = λ x . λ Δx . g (x ⊕ Δx) ⊝ f x
  -- f ⊕ Δf = λ x . f x ⊕ Δf x (x ⊝ x)

  -- We provide: terms for ⊕ and ⊝ on arbitrary types.
  apply-term : ∀ {τ Γ} → Term Γ (ΔType τ ⇒ τ ⇒ τ)
  diff-term : ∀ {τ Γ} → Term Γ (τ ⇒ τ ⇒ ΔType τ)
  nil-term : ∀ {τ Γ} → Term Γ (τ ⇒ ΔType τ)

  apply-term {base ι} = apply-base
  apply-term {σ ⇒ τ} =
    let
       _⊕τ_ = λ {Γ} t Δt → app₂ (apply-term {τ} {Γ}) Δt t
       nil-σ = λ {Γ} t → app (nil-term {σ} {Γ}) t
     in
       absV 3 (λ Δh h y → app h y ⊕τ app (app Δh y) (nil-σ y))

  diff-term {base ι} = diff-base
  diff-term {σ ⇒ τ} =
    let
       _⊝τ_ = λ {Γ} s t  → app₂ (diff-term {τ} {Γ}) s t
       _⊕σ_ = λ {Γ} t Δt → app₂ (apply-term {σ} {Γ}) Δt t
     in
       absV 4 (λ g f x Δx → app g (x ⊕σ Δx) ⊝τ app f x)

  nil-term {base ι} = nil-base
  nil-term {σ ⇒ τ} =
    -- What I'd usually write:
    --absV 1 (λ f → app₂ diff-term f f)
    -- What I wrote in fact:
    let
       _⊝τ_ = λ {Γ} s t  → app₂ (diff-term {τ} {Γ}) s t
       _⊕σ_ = λ {Γ} t Δt → app₂ (apply-term {σ} {Γ}) Δt t
     in
       absV 1 (λ ff → app (absV 3 (λ f x Δx → app f (x ⊕σ Δx) ⊝τ app f x)) ff)
    -- This simplified a lot proving meaning-onil by reusing meaning-⊝.
    --
    -- The reason is that the extra lambda-abstraction ensures that f is pushed
    -- twice in the environment.

  apply : ∀ τ {Γ} →
    Term Γ (ΔType τ) → Term Γ τ →
    Term Γ τ
  apply _ = app₂ apply-term

  diff : ∀ τ {Γ} →
    Term Γ τ → Term Γ τ →
    Term Γ (ΔType τ)
  diff _ = app₂ diff-term

  onil₍_₎ : ∀ τ {Γ} →
    Term Γ τ →
    Term Γ (ΔType τ)
  onil₍ _ ₎ = app nil-term

  infixl 6 apply diff

  syntax apply τ x Δx = Δx ⊕₍ τ ₎ x
  syntax diff τ x y = x ⊝₍ τ ₎ y

  infixl 6 _⊕_ _⊝_

  _⊕_ : ∀ {τ Γ} →
    Term Γ (ΔType τ) → Term Γ τ →
    Term Γ τ
  _⊕_ {τ} = apply τ

  _⊝_ : ∀ {τ Γ} →
    Term Γ τ → Term Γ τ →
    Term Γ (ΔType τ)
  _⊝_ {τ} = diff τ

  onil : ∀ {τ Γ} →
    Term Γ τ →
    Term Γ (ΔType τ)
  onil {τ} = onil₍ τ ₎
