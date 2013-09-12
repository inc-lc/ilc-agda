import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Change.Type as ChangeType

module Parametric.Change.Derive
    {Base : Set {- of base types -}}
    {Constant : Type.Context Base → Type.Type Base → Set {- of constants -}}
    (ΔBase : Base → Base)
    (deriveConst :
      ∀ {Γ Σ τ} → Constant Σ τ →
      Term.Terms
        Constant
        (ChangeType.ΔContext ΔBase Γ)
        (ChangeType.ΔContext ΔBase Σ) →
      Term.Term Constant (ChangeType.ΔContext ΔBase Γ) (ChangeType.ΔType ΔBase τ))
  where

-- Terms of languages described in Plotkin style

open Type Base
open Term Constant
open ChangeType ΔBase

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
