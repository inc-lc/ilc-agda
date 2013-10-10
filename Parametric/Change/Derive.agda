import Parametric.Syntax.Type as Type
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

Structure : Set
Structure = ∀ {Γ Σ τ} →
  Const Σ τ →
  Terms (ΔContext Γ) Σ →
  Terms (ΔContext Γ) (mapContext ΔType Σ) →
  Term (ΔContext Γ) (ΔType τ)

module Structure (deriveConst : Structure) where
  fit : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) τ
  fit = weaken Γ≼ΔΓ

  fit-terms : ∀ {Σ Γ} → Terms Γ Σ → Terms (ΔContext Γ) Σ
  fit-terms = weaken-terms Γ≼ΔΓ

  deriveVar : ∀ {τ Γ} → Var Γ τ → Var (ΔContext Γ) (ΔType τ)
  deriveVar this = this
  deriveVar (that x) = that (that (deriveVar x))

  derive-terms : ∀ {Σ Γ} → Terms Γ Σ → Terms (ΔContext Γ) (mapContext ΔType Σ)
  derive : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) (ΔType τ)

  derive-terms {∅}    ∅ = ∅
  derive-terms {τ • Σ} (t • ts) = derive t • derive-terms ts

  derive (var x) = var (deriveVar x)
  derive (app s t) = app (app (derive s) (fit t)) (derive t)
  derive (abs t) = abs (abs (derive t))
  derive (const c ts) = deriveConst c (fit-terms ts) (derive-terms ts)
