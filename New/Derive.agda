module New.Derive where
open import New.Lang
open import New.Changes

open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Sum
open import Data.Product

ΔΓ : Context → Context
ΔΓ ∅ = ∅
ΔΓ (τ • Γ) = Δt τ • τ • ΔΓ Γ

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ ΔΓ Γ
Γ≼ΔΓ {∅} = ∅
Γ≼ΔΓ {τ • Γ} = drop Δt τ • keep τ • Γ≼ΔΓ

deriveConst : ∀ {τ} →
  Const τ →
  Term ∅ (Δt τ)
deriveConst ()

deriveVar : ∀ {Γ τ} → Var Γ τ → Var (ΔΓ Γ) (Δt τ)
deriveVar this = this
deriveVar (that x) = that (that (deriveVar x))

fit : ∀ {τ Γ} → Term Γ τ → Term (ΔΓ Γ) τ
fit = weaken Γ≼ΔΓ

derive : ∀ {Γ τ} → Term Γ τ → Term (ΔΓ Γ) (Δt τ)
derive (const c) = weaken (∅≼Γ {ΔΓ _}) (deriveConst c)
derive (var x) = var (deriveVar x)
derive (app s t) = app (app (derive s) (fit t)) (derive t)
derive (abs t) = abs (abs (derive t))
