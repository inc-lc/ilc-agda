module Thesis.SIRelBigStep.DSyntax where

open import Thesis.SIRelBigStep.Syntax public

-- data DType : Set where
--   _⇒_ : (σ τ : DType) → DType
--   int : DType
DType = Type

import Base.Syntax.Context
module DC = Base.Syntax.Context DType

Δτ : Type → DType
Δτ (σ ⇒ τ) = σ ⇒ Δτ σ ⇒ Δτ τ
Δτ (pair τ1 τ2) = pair (Δτ τ1) (Δτ τ2)
Δτ nat = nat

ΔΔ : Context → DC.Context
ΔΔ ∅ = ∅
ΔΔ (τ • Γ) = Δτ τ • ΔΔ Γ
--ΔΔ Γ = Γ

-- A DTerm evaluates in normal context Δ, change context (ΔΔ Δ), and produces
-- a result of type (Δt τ).
data DTerm (Δ : Context) (τ : DType) : Set
data DSVal (Δ : Context) : (τ : DType) → Set where
  dvar : ∀ {τ} →
    (x : Var Δ τ) →
    DSVal Δ τ
  dabs : ∀ {σ τ}
    (dt : DTerm (σ • Δ) τ) →
    DSVal Δ (σ ⇒ τ)
  dcons : ∀ {τ1 τ2}
    (dsv1 : DSVal Δ τ1)
    (dsv2 : DSVal Δ τ2) →
    DSVal Δ (pair τ1 τ2)
  dconst : ∀ {τ} → (dc : Const (Δτ τ)) → DSVal Δ τ

data DTerm (Δ : Context) (τ : DType) where
  dval :
    DSVal Δ τ →
    DTerm Δ τ
  dprimapp : ∀ {σ}
    (p : Primitive (σ ⇒ τ)) →
    (sv : SVal Δ σ) →
    (dsv : DSVal Δ σ) →
    DTerm Δ τ
  dapp : ∀ {σ}
    (dvs : DSVal Δ (σ ⇒ τ)) →
    (vt : SVal Δ σ) →
    (dvt : DSVal Δ σ) →
    DTerm Δ τ
  dlett : ∀ {σ}
    (s : Term Δ σ) →
    (ds : DTerm Δ σ) →
    (dt : DTerm (σ • Δ) τ) →
    DTerm Δ τ
