module Thesis.SIRelBigStep.DOpSem where

open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Thesis.SIRelBigStep.DLangDerive public
open import Thesis.SIRelBigStep.OpSem public
open import Thesis.SIRelBigStep.DSyntax public

data DVal : Type → Set
import Base.Denotation.Environment
module D = Base.Denotation.Environment DType DVal

ChΔ : ∀ (Δ : Context) → Set
ChΔ Δ = D.⟦ Δ ⟧Context

data DVal where
  bang : ∀ {τ} → Val τ → DVal τ
  dclosure : ∀ {Γ σ τ} → (dt : DTerm (σ • Γ) τ) → (ρ : ⟦ Γ ⟧Context) →  (dρ : ChΔ Γ) → DVal (σ ⇒ τ)
  dnatV : ∀ (n : ℕ) → DVal nat

_⊕_ : ∀ {τ} → (v1 : Val τ) (dv : DVal τ) → Val τ

_⊕ρ_ : ∀ {Γ} → ⟦ Γ ⟧Context → ChΔ Γ → ⟦ Γ ⟧Context
∅ ⊕ρ ∅ = ∅
(v • ρ1) ⊕ρ (dv • dρ) = v ⊕ dv • ρ1 ⊕ρ dρ

v1 ⊕ bang v2 = v2
closure {Γ} t ρ ⊕ dclosure {Γ1} dt ρ₁ dρ with Γ ≟Ctx Γ1
closure {Γ} t ρ ⊕ dclosure {.Γ} dt ρ₁ dρ | yes refl = closure t (ρ ⊕ρ dρ)
... | no ¬p = closure t ρ
_⊕_ (natV n) (dnatV dn) = natV (n + dn)

data _D_⊢_↓_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) : ∀ {τ} → DTerm Γ τ → DVal τ → Set where
  dabs : ∀ {σ τ} {dt : DTerm (σ • Γ) τ} →
    ρ D dρ ⊢ dval (dabs dt) ↓ dclosure dt ρ dρ
  dvar : ∀ {τ} (x : DC.Var Γ τ) →
    ρ D dρ ⊢ dval (dvar (derive-dvar x)) ↓ D.⟦ x ⟧Var dρ
  dlit : ∀ n →
    ρ D dρ ⊢ dconst (lit n) ↓ dnatV 0
  dapp : ∀ {hasIdx} {n : Idx hasIdx}
    {Γ′ σ τ ρ′ dρ′}
    {dvs} {vt} {dvt}
    {vtv} {dvtv}
    {dt : DTerm (σ • Γ′) τ} {dv} →
    ρ D dρ ⊢ dval dvs ↓ dclosure dt ρ′ dρ′ →
    ρ ⊢ val vt ↓[ n ] vtv →
    ρ D dρ ⊢ dval dvt ↓ dvtv →
    (vtv • ρ′) D (dvtv • dρ′) ⊢ dt ↓ dv →
    ρ D dρ ⊢ dapp dvs vt dvt ↓ dv
  dlett : ∀ {hasIdx} {n : Idx hasIdx}
    {σ τ} {s : Term Γ σ} {ds} {dt : DTerm (σ • Γ) τ}
    {vsv dvsv dv} →
    ρ ⊢ s ↓[ n ] vsv →
    ρ D dρ ⊢ ds ↓ dvsv →
    (vsv • ρ) D (dvsv • dρ) ⊢ dt ↓ dv →
    ρ D dρ ⊢ dlett s ds dt ↓ dv
  bangapp : ∀ {hasIdx} {n1 n2 : Idx hasIdx}
    {Γ′ σ τ ρ′}
    {dvs} {vt} {dvt}
    {vtv2}
    {t : Term (σ • Γ′) τ} {v2} →
    ρ D dρ ⊢ dval dvs ↓ bang (closure t ρ′) →
    (ρ ⊕ρ dρ) ⊢ val vt ↓[ n1 ] vtv2 →
    (vtv2 • ρ′) ⊢ t ↓[ n2 ] v2 →
    ρ D dρ ⊢ dapp dvs vt dvt ↓ bang v2
