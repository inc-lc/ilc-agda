import Parametric.Syntax.Type as Type
import Base.Syntax.Context as Context
import Parametric.Syntax.Term as Term
import Syntax.DeltaContext as DeltaContext
import Parametric.Change.Type as ChangeType

module Syntax.Derive.Plotkin
    {Base : Set {- of base types -}}
    {Constant : Context.Context (Type.Type Base) → Type.Type Base → Set {- of constants -}}
    (ΔBase : Base → Base)
    (deriveConst :
      ∀ {Γ Σ τ} → Constant Σ τ →
      Term.Terms
        Constant
        (DeltaContext.ΔContext (ChangeType.ΔType ΔBase) Γ)
        (DeltaContext.ΔContext (ChangeType.ΔType ΔBase) Σ) →
      Term.Term Constant (DeltaContext.ΔContext (ChangeType.ΔType ΔBase) Γ) (ChangeType.ΔType ΔBase τ))
  where

-- Terms of languages described in Plotkin style

open Type Base
open Context Type
open Term Constant
open ChangeType ΔBase
open DeltaContext ΔType

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
