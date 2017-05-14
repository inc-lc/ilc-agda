module Thesis.ANormalDTerm where

open import Thesis.ANormal


ΔΔ : Context → Context
ΔΔ ∅ = ∅
ΔΔ (τ • Γ) = Δt τ • ΔΔ Γ
Δτ = Δt

ChΔ : ∀ (Δ : Context) → Set
ChΔ Δ = ⟦ ΔΔ Δ ⟧Context

-- [_]Δ_from_to_ : ∀ Δ → ChΔ Δ → (ρ1 ρ2 : ⟦ Δ ⟧Context) → Set
-- [ ∅ ]Δ ∅ from ∅ to ∅ = ⊤
-- [ τ • Δ ]Δ dv • dρ from v1 • ρ1 to (v2 • ρ2) = [ τ ]τ dv from v1 to v2 × [ Δ ]Δ dρ from ρ1 to ρ2

data [_]Δ_from_to_ : ∀ Δ → ChΔ Δ → (ρ1 ρ2 : ⟦ Δ ⟧Context) → Set where
  v∅ : [ ∅ ]Δ ∅ from ∅ to ∅
  _v•_ : ∀ {τ Δ dv v1 v2 dρ ρ1 ρ2} →
    (dvv : [ τ ]τ dv from v1 to v2) →
    (dρρ : [ Δ ]Δ dρ from ρ1 to ρ2) →
    [ τ • Δ ]Δ (dv • dρ) from (v1 • ρ1) to (v2 • ρ2)

derive-dvar : ∀ {Δ σ} → (x : Var Δ σ) → Var (ΔΔ Δ) (Δτ σ)
derive-dvar this = this
derive-dvar (that x) = that (derive-dvar x)

fromtoDeriveDVar : ∀ {Δ τ} → (x : Var Δ τ) →
  ∀ {dρ ρ1 ρ2} → [ Δ ]Δ dρ from ρ1 to ρ2 →
  [ τ ]τ (⟦ derive-dvar x ⟧Var dρ) from (⟦ x ⟧Var ρ1) to (⟦ x ⟧Var ρ2)
fromtoDeriveDVar this (dvv v• dρρ) = dvv
fromtoDeriveDVar (that x) (dvv v• dρρ) = fromtoDeriveDVar x dρρ

-- A DTerm evaluates in normal context Δ, change context (ΔΔ Δ), and produces
-- a result of type (Δt τ).
data DTerm : (Δ : Context) (τ : Type) → Set where
  dvar : ∀ {Δ τ} (x : Var (ΔΔ Δ) (Δt τ)) →
    DTerm Δ τ
  dlett : ∀ {Δ τ σ τ₁} →
    (f : Var Δ (σ ⇒ τ₁)) →
    (x : Var Δ σ) →
    (t : Term (τ₁ • Δ) τ) →
    (df : Var (ΔΔ Δ) (Δτ (σ ⇒ τ₁))) →
    (dx : Var (ΔΔ Δ) (Δτ σ)) →
    (dt : DTerm (τ₁ • Δ) τ) →
    DTerm Δ τ

data DFun (Δ : Context) : (τ : Type) → Set where
  dterm : ∀ {τ} → DTerm Δ τ → DFun Δ τ
  dabs : ∀ {σ τ} → DFun (σ • Δ) τ → DFun Δ (σ ⇒ τ)

derive-dterm : ∀ {Δ σ} → (t : Term Δ σ) → DTerm Δ σ
derive-dterm (var x) = dvar (derive-dvar x)
derive-dterm (lett f x t) =
  dlett f x t (derive-dvar f) (derive-dvar x) (derive-dterm t)

⟦_⟧DTerm : ∀ {Δ τ} → DTerm Δ τ → ⟦ Δ ⟧Context → ⟦ ΔΔ Δ ⟧Context → ⟦ Δt τ ⟧Type
⟦ dvar x ⟧DTerm ρ dρ = ⟦ x ⟧Var dρ
⟦ dlett f x t df dx dt ⟧DTerm ρ dρ =
  let v = (⟦ x ⟧Var ρ)
  in
    ⟦ dt ⟧DTerm
      (⟦ f ⟧Var ρ v • ρ)
      (⟦ df ⟧Var dρ v (⟦ dx ⟧Var dρ) • dρ)

fromtoDeriveDTerm : ∀ {Δ τ} → (t : Term Δ τ) →
  ∀ {dρ ρ1 ρ2} → [ Δ ]Δ dρ from ρ1 to ρ2 →
  [ τ ]τ (⟦ derive-dterm t ⟧DTerm ρ1 dρ) from (⟦ t ⟧Term ρ1) to (⟦ t ⟧Term ρ2)
fromtoDeriveDTerm (var x) dρρ = fromtoDeriveDVar x dρρ
fromtoDeriveDTerm (lett f x t) dρρ =
  let fromToF = fromtoDeriveDVar f dρρ
      fromToX = fromtoDeriveDVar x dρρ
      fromToFX = fromToF _ _ _ fromToX
  in fromtoDeriveDTerm t (fromToFX v• dρρ)

derive-dfun : ∀ {Δ σ} → (t : Fun Δ σ) → DFun Δ σ
derive-dfun (term t) = dterm (derive-dterm t)
derive-dfun (abs f) = dabs (derive-dfun f)

⟦_⟧DFun : ∀ {Δ τ} → DFun Δ τ → ⟦ Δ ⟧Context → ⟦ ΔΔ Δ ⟧Context → ⟦ Δt τ ⟧Type
⟦ dterm t ⟧DFun = ⟦ t ⟧DTerm
⟦ dabs df ⟧DFun ρ dρ = λ v dv → ⟦ df ⟧DFun (v • ρ) (dv • dρ)

fromtoDeriveDFun : ∀ {Δ τ} → (f : Fun Δ τ) →
  ∀ {dρ ρ1 ρ2} → [ Δ ]Δ dρ from ρ1 to ρ2 →
  [ τ ]τ (⟦ derive-dfun f ⟧DFun ρ1 dρ) from (⟦ f ⟧Fun ρ1) to (⟦ f ⟧Fun ρ2)
fromtoDeriveDFun (term t) = fromtoDeriveDTerm t
fromtoDeriveDFun (abs f) dρρ = λ dv v1 v2 dvv → fromtoDeriveDFun f (dvv v• dρρ)
