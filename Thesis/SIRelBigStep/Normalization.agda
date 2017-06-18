module Thesis.SIRelBigStep.Normalization where

open import Thesis.SIRelBigStep.Lang

open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Relation.Binary.PropositionalEquality

mutual
  normT : ∀ {Γ} τ (t : Term Γ τ) (ρ : ⟦ Γ ⟧Context) → Set
  normT τ t ρ = Σ[ v ∈ Val τ ] ρ ⊢ t ↓[ no ] v × normV τ v

  normV : ∀ τ (v : Val τ) → Set
  normV (σ ⇒ τ) (closure t ρ) = ∀ (v : Val σ) → (vv : normV _ v) → normT τ t (v • ρ)
  normV (pair τ1 τ2) (pairV v1 v2) = normV _ v1 × normV _ v2
  normV nat (natV n) = ⊤

normρ : ∀ Γ (ρ : ⟦ Γ ⟧Context) → Set
normρ ∅ ∅ = ⊤
normρ (τ • Γ) (v • ρ) = normV τ v × normρ Γ ρ

⟦_⟧VarNorm : ∀ {Γ τ} (x : Var Γ τ) {ρ} →
  normρ Γ ρ →
  normV τ (⟦ x ⟧Var ρ)
⟦ this ⟧VarNorm   {v • ρ} (vv , ρρ) = vv
⟦ that x ⟧VarNorm {v • ρ} (vv , ρρ) = ⟦ x ⟧VarNorm ρρ

normT-fund : ∀ {τ Γ} (t : Term Γ τ) ρ (ρρ : normρ Γ ρ) →
  normT τ t ρ

normV-fund-const : ∀ {τ} (c : Const τ) → normV τ (eval-const c)
normV-fund-const (lit n) = tt

normV-fund-sval : ∀ {τ Γ} (sv : SVal Γ τ) ρ (ρρ : normρ Γ ρ) → normV τ (eval sv ρ)
normV-fund-sval (var x) ρ ρρ = ⟦ x ⟧VarNorm ρρ
normV-fund-sval (abs t) ρ ρρ v vv = normT-fund t (v • ρ) (vv , ρρ)
normV-fund-sval (cons sv1 sv2) ρ ρρ = normV-fund-sval sv1 ρ ρρ , normV-fund-sval sv2 ρ ρρ
normV-fund-sval (const c) ρ ρρ = normV-fund-const c

-- Not inlined because it gives the right type ascription to the derivation `val sv`.
normT-fund-sval : ∀ {τ Γ} (sv : SVal Γ τ) ρ (ρρ : normρ Γ ρ) → normT τ (val sv) ρ
normT-fund-sval sv ρ ρρ = eval sv ρ , val sv , normV-fund-sval sv ρ ρρ

normV-fund-primitive : ∀ {σ τ} p →
  ∀ v → (vv : normV σ v) →
  normV τ (eval-primitive p v)
normV-fund-primitive succ (natV n) vv = tt
normV-fund-primitive add (pairV (natV m) (natV n)) vv = tt

open import Data.Nat
normT-fund (val sv) ρ ρρ = normT-fund-sval sv ρ ρρ
normT-fund (primapp p sv) ρ ρρ = eval-primitive p (eval sv ρ) , primapp p sv , normV-fund-primitive p (eval sv ρ) (normV-fund-sval sv ρ ρρ)
normT-fund (app vs vt) ρ ρρ with normT-fund-sval vs ρ ρρ | normT-fund-sval vt ρ ρρ
... | closure t ρ₁ , ↓fv , fvv | av , ↓av , avv with fvv av avv
... | v , ↓v , vv = v , app zero _ ↓fv ↓av ↓v , vv
normT-fund (lett s t) ρ ρρ with normT-fund s ρ ρρ
... | sv , ↓s , svv with normT-fund t (sv • ρ) (svv , ρρ)
... | tv , ↓t , tvv = tv , lett zero zero sv s t ↓s ↓t , tvv

normalize : ∀ {τ} (t : Term ∅ τ) → Σ[ v ∈ Val τ ] ∅ ⊢ t ↓[ no ] v
normalize t with normT-fund t ∅ tt
... | v , ↓ , _ = v , ↓
