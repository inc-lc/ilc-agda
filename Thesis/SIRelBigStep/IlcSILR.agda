module Thesis.SIRelBigStep.IlcSILR where

open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Thesis.SIRelBigStep.Lang public
open import Thesis.SIRelBigStep.DLang public

open import Thesis.SIRelBigStep.ArithExtra public

rrelT3-skeleton :
  ∀ {τ Γ} →
  ((v1 : Val τ) → (dv : DVal τ) → (v2 : Val τ) → (k : ℕ) → Set) →
  (t1 : Term Γ τ) (dt : DTerm Γ τ) (t2 : Term Γ τ)
  (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) →
  ℕ → Set
rrelT3-skeleton {τ} ternary-rel t1 dt t2 ρ1 dρ ρ2 k =
  (v1 v2 : Val τ) →
  ∀ j (j<k : j < k) →
  (ρ1⊢t1↓[j]v1 : ρ1 ⊢ t1 ↓[ i' j ] v1) →
  (ρ2⊢t2↓[n2]v2 : ρ2 ⊢ t2 ↓[ no ] v2) →
  Σ[ dv ∈ DVal τ ]
  ρ1 D dρ ⊢ dt ↓ dv ×
  ternary-rel v1 dv v2 (k ∸ j)

mutual
  rrelT3 : ∀ {τ Γ} (t1 : Term Γ τ) (dt : DTerm Γ τ) (t2 : Term Γ τ) (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
  rrelT3 {τ} = rrelT3-skeleton (rrelV3 τ)

  rrelV3 : ∀ τ (v1 : Val τ) (dv : DVal τ) (v2 : Val τ) → (n : ℕ) → Set
  -- Making this case first ensures rrelV3 splits on its second argument, hence
  -- that all its equations hold definitionally.
  rrelV3 τ v1 (bang v2) v2' n = v2 ≡ v2'
  rrelV3 nat (natV v1) (dnatV dv) (natV v2) n = dv + v1 ≡ v2
  rrelV3 (σ ⇒ τ) (closure {Γ1} t1 ρ1) (dclosure {ΔΓ} dt ρ dρ) (closure {Γ2} t2 ρ2) n =
      Σ ((Γ1 ≡ Γ2) × (Γ1 ≡ ΔΓ)) λ { (refl , refl) →
        ρ1 ≡ ρ ×
        ρ1 ⊕ρ dρ ≡ ρ2 ×
        t1 ≡ t2 ×
        dt ≡ derive-dterm t1 ×
        ∀ (k : ℕ) (k<n : k < n) v1 dv v2 →
        rrelV3 σ v1 dv v2 k →
        rrelT3
          t1
          dt
          t2
          (v1 • ρ1)
          (dv • dρ)
          (v2 • ρ2)
          k
      }
  rrelV3 (pair τ1 τ2) (pairV va1 vb1) (dpairV dva dvb) (pairV va2 vb2) n =
    rrelV3 τ1 va1 dva va2 n × rrelV3 τ2 vb1 dvb vb2 n

rrelV3→⊕ : ∀ {τ n} v1 dv v2 → rrelV3 τ v1 dv v2 n → v1 ⊕ dv ≡ v2
rrelV3→⊕ v1 (bang v2) v2' vv = vv
rrelV3→⊕ (closure {Γ} t ρ) (dclosure .(derive-dterm t) .ρ dρ) (closure .t .(ρ ⊕ρ dρ)) ((refl , refl) , refl , refl , refl , refl , dvv) with Γ ≟Ctx Γ | ≟Ctx-refl Γ
... | .(yes refl) | refl = refl
rrelV3→⊕ (natV n) (dnatV dn) (natV .(dn + n)) refl rewrite +-comm n dn = refl
rrelV3→⊕ (pairV va1 vb1) (dpairV dva dvb) (pairV va2 vb2) (vaa , vbb) rewrite rrelV3→⊕  va1 dva va2 vaa | rrelV3→⊕ vb1 dvb vb2 vbb = refl

rrelρ3 : ∀ Γ (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
rrelρ3 ∅ ∅ ∅ ∅ n = ⊤
rrelρ3 (τ • Γ) (v1 • ρ1) (dv • dρ) (v2 • ρ2) n = rrelV3 τ v1 dv v2 n × rrelρ3 Γ ρ1 dρ ρ2 n

rrelρ3→⊕ : ∀ {Γ n} ρ1 dρ ρ2 → rrelρ3 Γ ρ1 dρ ρ2 n → ρ1 ⊕ρ dρ ≡ ρ2
rrelρ3→⊕ ∅ ∅ ∅ tt = refl
rrelρ3→⊕ (v1 • ρ1) (dv • dρ) (v2 • ρ2) (vv , ρρ) rewrite rrelV3→⊕ v1 dv v2 vv | rrelρ3→⊕ ρ1 dρ ρ2 ρρ = refl

rrelV3-mono : ∀ m n → m ≤ n → ∀ τ v1 dv v2 → rrelV3 τ v1 dv v2 n → rrelV3 τ v1 dv v2 m
rrelV3-mono m n m≤n τ v1 (bang v2) v2′ vv = vv
rrelV3-mono m n m≤n (σ ⇒ τ) (closure t ρ) (dclosure dt ρ₁ dρ) (closure t₁ ρ₂)
  -- Validity
  ((refl , refl) , refl , refl , refl , refl , vv) =
  (refl  , refl) , refl , refl , refl , refl , λ k k<m → vv k (≤-trans k<m m≤n)
rrelV3-mono m n m≤n nat (natV n₁) (dnatV n₂) (natV n₃) vv = vv
rrelV3-mono m n m≤n (pair τ1 τ2) (pairV va1 vb1) (dpairV dva dvb) (pairV va2 vb2) (vaa , vbb) =
  rrelV3-mono m n m≤n τ1 va1 dva va2 vaa , rrelV3-mono m n m≤n τ2 vb1 dvb vb2 vbb

rrelρ3-mono : ∀ m n → m ≤ n → ∀ Γ ρ1 dρ ρ2 → rrelρ3 Γ ρ1 dρ ρ2 n → rrelρ3 Γ ρ1 dρ ρ2 m
rrelρ3-mono m n m≤n ∅ ∅ ∅ ∅ tt = tt
rrelρ3-mono m n m≤n (τ • Γ) (v1 • ρ1) (dv • dρ) (v2 • ρ2) (vv , ρρ) = rrelV3-mono m n m≤n _ v1 dv v2 vv , rrelρ3-mono m n m≤n Γ ρ1 dρ ρ2 ρρ

⟦_⟧RelVar3 : ∀ {Γ τ n} (x : Var Γ τ) {ρ1 dρ ρ2} →
  rrelρ3 Γ ρ1 dρ ρ2 n →
  rrelV3 τ (⟦ x ⟧Var ρ1) (D.⟦ x ⟧Var dρ) (⟦ x ⟧Var ρ2) n
⟦ this ⟧RelVar3   {v1 • ρ1} {dv • dρ} {v2 • ρ2} (vv , ρρ) = vv
⟦ that x ⟧RelVar3 {v1 • ρ1} {dv • dρ} {v2 • ρ2} (vv , ρρ) = ⟦ x ⟧RelVar3 ρρ

-- Direct analogue of rrelV3→⊕ for rrelT3: simply say that the resulting values
-- are related.
-- Alternatively, one could try internalizing ⊕ and giving some term equivalence, but it does not seem worthwhile.
rrelT3→⊕ : ∀ {τ Γ k}
  (t1 : Term Γ τ) (dt : DTerm Γ τ) (t2 : Term Γ τ) (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) →
  rrelT3 {τ} t1 dt t2 ρ1 dρ ρ2 k →
  rrelT3-skeleton (λ v1 dv v2 _ → v1 ⊕ dv ≡ v2) t1 dt t2 ρ1 dρ ρ2 k
rrelT3→⊕ t1 dt t2 ρ1 dρ ρ2 ttrel v1 v2 j j<k ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2 with ttrel v1 v2 j j<k ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2
... | dv , ↓dv , vv = dv , ↓dv , rrelV3→⊕ v1 dv v2 vv
