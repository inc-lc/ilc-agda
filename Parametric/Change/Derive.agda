------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Incrementalization as term-to-term transformation (Fig. 4g).
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
open import Base.Data.DependentList
import Parametric.Syntax.Term as Term
import Parametric.Change.Type as ChangeType

module Parametric.Change.Derive
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (ΔBase : ChangeType.Structure Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open ChangeType.Structure Base ΔBase

-- Extension point: Incrementalization of primitives.
Structure : Set
Structure = ∀ {τ} →
  Const τ →
  Term ∅ (ΔType τ)

module Structure (derive-const : Structure) where
  fit : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) τ
  fit = weaken Γ≼ΔΓ

  -- In the paper, we transform "x" to "dx". Here, we work with
  -- de Bruijn indices, so we have to manipulate the indices to
  -- account for a bigger context after transformation.
  deriveVar : ∀ {τ Γ} → Var Γ τ → Var (ΔContext Γ) (ΔType τ)
  deriveVar this = this
  deriveVar (that x) = that (that (deriveVar x))

  -- We provide: Incrementalization of arbitrary terms.
  derive : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) (ΔType τ)
  derive (var x) = var (deriveVar x)
  derive (app s t) = app (app (derive s) (fit t)) (derive t)
  derive (abs t) = abs (abs (derive t))
  derive {Γ = Γ} (const c) = weaken (∅≼Γ {ΔContext Γ}) (derive-const c)
