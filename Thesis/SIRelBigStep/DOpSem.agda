{-# OPTIONS --exact-split #-}
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
  dpairV : ∀ {σ τ} → DVal σ → DVal τ → DVal (pair σ τ)

_⊕_ : ∀ {τ} → (v1 : Val τ) (dv : DVal τ) → Val τ

_⊕ρ_ : ∀ {Γ} → ⟦ Γ ⟧Context → ChΔ Γ → ⟦ Γ ⟧Context
∅ ⊕ρ ∅ = ∅
(v • ρ1) ⊕ρ (dv • dρ) = v ⊕ dv • ρ1 ⊕ρ dρ

v1 ⊕ bang v2 = v2
closure {Γ} t ρ ⊕ dclosure {Γ1} dt ρ₁ dρ with Γ ≟Ctx Γ1
closure {Γ} t ρ ⊕ dclosure {.Γ} dt ρ₁ dρ | yes refl = closure t (ρ ⊕ρ dρ)
... | no ¬p = closure t ρ
natV n ⊕ dnatV dn = natV (n + dn)
pairV v1 v2 ⊕ dpairV dv1 dv2 = pairV (v1 ⊕ dv1) (v2 ⊕ dv2)

inv-Δτ-nat : ∀ τ → Δτ τ ≡ nat → τ ≡ nat
inv-Δτ-nat nat refl = refl
inv-Δτ-nat (τ ⇒ τ₁) ()
inv-Δτ-nat (pair τ τ₁) ()

deval-const : ∀ {τ} → Const (Δτ τ) → DVal τ
deval-const {σ} c with Δτ σ | inv-Δτ-nat σ
deval-const {σ} (lit n) | .nat | inv-σ with inv-σ refl
deval-const {.nat} (lit n) | .nat | inv-σ | refl = dnatV n

deval : ∀ {Γ τ} (sv : DSVal Γ τ) (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) → DVal τ
deval (dvar x) ρ dρ = D.⟦ x ⟧Var dρ
deval (dabs dt) ρ dρ = dclosure dt ρ dρ
deval (dcons dsv1 dsv2) ρ dρ = dpairV (deval dsv1 ρ dρ) (deval dsv2 ρ dρ)
deval (dconst c) ρ dρ = deval-const c

deval-primitive : ∀ {σ τ} → Primitive (σ ⇒ τ) → Val σ → DVal σ → DVal τ
deval-primitive succ (natV _) (bang (natV n2)) = bang (natV (suc n2))
deval-primitive succ (natV n) (dnatV dn) = dnatV dn
deval-primitive add (pairV _ _) (dpairV (dnatV da) (dnatV db)) = dnatV (da + db)
deval-primitive add (pairV _ _) (bang p2) = bang (eval-primitive add p2)
-- During the proof we need to know which clauses hold definitionally, and sadly we can't get a single equation here.
deval-primitive add p1 @ (pairV a1 b1) dp @ (dpairV (dnatV da) (bang b2)) = bang (eval-primitive add (p1 ⊕ dp))
deval-primitive add p1 @ (pairV a1 b1) dp @ (dpairV (bang a2) db) = bang (eval-primitive add (p1 ⊕ dp))

deval-derive-const-inv : ∀ {τ Γ} (c : Const τ) (ρ : ⟦ Γ ⟧Context) dρ → deval (derive-const c) ρ dρ ≡ deval (derive-const c) ∅ ∅
deval-derive-const-inv (lit n) ρ dρ = refl

data _D_⊢_↓_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) : ∀ {τ} → DTerm Γ τ → DVal τ → Set where
  dval : ∀ {τ} (sv : DSVal Γ τ) →
    ρ D dρ ⊢ dval sv ↓ deval sv ρ dρ
  dprimapp : ∀ {σ τ} (p : Primitive (σ ⇒ τ)) (sv : SVal Γ σ) dsv →
    ρ D dρ ⊢ dprimapp p sv dsv ↓ deval-primitive p (eval sv ρ) (deval dsv ρ dρ)
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
