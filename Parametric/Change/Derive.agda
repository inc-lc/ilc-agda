import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Change.Type as ChangeType

module Parametric.Change.Derive
    {Base : Type.Structure}
    (Constant : Term.Structure Base)
    (ΔBase : ChangeType.Structure Base)
  where

open Type.Structure Base
open Term.Structure Base Constant
open ChangeType.Structure Base ΔBase

Structure : Set
Structure = ∀ {Γ Σ τ} →
  Constant Σ τ →
  Terms (ΔContext Γ) (ΔContext Σ) →
  Term (ΔContext Γ) (ΔType τ)

module Structure (deriveConst : Structure) where
  fit : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) τ
  fit = weaken Γ≼ΔΓ

  deriveVar : ∀ {τ Γ} → Var Γ τ → Var (ΔContext Γ) (ΔType τ)
  deriveVar this = this
  deriveVar (that x) = that (that (deriveVar x))

  derive-terms : ∀ {Σ Γ} → Terms Γ Σ → Terms (ΔContext Γ) (ΔContext Σ)
  derive : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) (ΔType τ)

  derive-terms {∅}    ∅ = ∅
  derive-terms {τ • Σ} (t • ts) = derive t • fit t • derive-terms ts

  derive (var x) = var (deriveVar x)
  derive (app s t) = app (app (derive s) (fit t)) (derive t)
  derive (abs t) = abs (abs (derive t))
  derive (const c ts) = deriveConst c (derive-terms ts)
