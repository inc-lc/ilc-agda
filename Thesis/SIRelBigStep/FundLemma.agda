module Thesis.SIRelBigStep.FundLemma where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Thesis.SIRelBigStep.IlcSILR

rfundamentalV3v : ∀ {Γ τ} (x : Var Γ τ) → (n : ℕ) → ∀ ρ1 dρ ρ2 (ρρ : rrelρ3 Γ ρ1 dρ ρ2 (suc n)) → rrelV3 τ (⟦ x ⟧Var ρ1) (D.⟦ x ⟧Var dρ) (⟦ x ⟧Var ρ2) n
rfundamentalV3v x n ρ1 dρ ρ2 ρρ = rrelV3-mono n (suc n) (≤-step ≤-refl) _ (⟦ x ⟧Var ρ1) (D.⟦ x ⟧Var dρ) (⟦ x ⟧Var ρ2) (⟦ x ⟧RelVar3 ρρ)

rfundamental3constV : ∀ {τ} k (c : Const τ) →
  rrelV3 τ (eval-const c) (deval (derive-const c) ∅ ∅) (eval-const c) k
rfundamental3constV k (lit n) = refl

rfundamental3 : ∀ {τ Γ} k (t : Term Γ τ) → ∀ ρ1 dρ ρ2 → (ρρ : rrelρ3 Γ ρ1 dρ ρ2 k) →
  rrelT3 t (derive-dterm t) t ρ1 dρ ρ2 k

rfundamental3svv : ∀ {τ Γ} k (sv : SVal Γ τ) →
  ∀ ρ1 dρ ρ2 → (ρρ : rrelρ3 Γ ρ1 dρ ρ2 (suc k)) → rrelV3 τ (eval sv ρ1) (deval (derive-dsval sv) ρ1 dρ) (eval sv ρ2) k
rfundamental3svv k (var x) ρ1 dρ ρ2 ρρ = rfundamentalV3v x k ρ1 dρ ρ2 ρρ
rfundamental3svv k (cons sv1 sv2) ρ1 dρ ρ2 ρρ = rfundamental3svv k sv1 ρ1 dρ ρ2 ρρ , rfundamental3svv k sv2 ρ1 dρ ρ2 ρρ
rfundamental3svv k (const c) ρ1 dρ ρ2 ρρ rewrite deval-derive-const-inv c ρ1 dρ = rfundamental3constV k c
rfundamental3svv k (abs t) ρ1 dρ ρ2 ρρ = (refl , refl) , refl , rrelρ3→⊕ ρ1 dρ ρ2 ρρ , refl , refl ,
    λ k₁ k<n v1 dv v2 vv →
    rfundamental3 k₁ t (v1 • ρ1) (dv • dρ) (v2 • ρ2) (vv , rrelρ3-mono k₁ (suc k) (≤-step (lt1 k<n)) _ _ _ _ ρρ)

rfundamental3sv : ∀ {τ Γ} k (sv : SVal Γ τ) →
  ∀ ρ1 dρ ρ2 → (ρρ : rrelρ3 Γ ρ1 dρ ρ2 k) → rrelT3 (val sv) (dval (derive-dsval sv)) (val sv) ρ1 dρ ρ2 k
rfundamental3sv (suc k) sv ρ1 dρ ρ2 ρρ .(eval sv ρ1) .(eval sv ρ2) .1 (s≤s j<k) (val .sv) (val .sv) = deval (derive-dsval sv) ρ1 dρ , dval (derive-dsval sv) , rfundamental3svv k sv ρ1 dρ ρ2 ρρ

open import Theorem.Groups-Nehemiah
rfundamental3primv : ∀ {σ τ} k p →
  ∀ v1 dv v2 → (vv : rrelV3 σ v1 dv v2 k) →
  rrelV3 τ (eval-primitive p v1) (deval-primitive p v1 dv) (eval-primitive p v2) k
rfundamental3primv k succ (natV n₁) (bang .(natV n)) (natV n) refl = refl
rfundamental3primv k succ (natV n) (dnatV dn) (natV .(dn + n)) refl = +-suc dn n
rfundamental3primv k add (pairV (natV a1) (natV b1))
  (dpairV (dnatV da) (dnatV db))
  (pairV (natV .(da + a1)) (natV .(db + b1)))
  (refl , refl) = ℕ-mn·pq=mp·nq {da} {db} {a1} {b1}
rfundamental3primv k add (pairV a1 b1)
  (dpairV (dnatV da) (bang b2))
  (pairV a2 .b2) (aa , refl) rewrite rrelV3→⊕ a1 (dnatV da) a2 aa = refl
rfundamental3primv k add (pairV a1 b1)
  (dpairV (bang a2) db)
  (pairV .a2 b2) (refl , bb) rewrite rrelV3→⊕ b1 db b2 bb = refl
rfundamental3primv k add (pairV a1 b1) (bang p2) .p2 refl = refl

-- Warning: names like ρ1⊢t1↓[j]v1 are all broken, sorry for not fixing them.
rfundamental3 k (val sv) = rfundamental3sv k sv
rfundamental3 (suc k) (primapp p sv) ρ1 dρ ρ2 ρρ
  .(eval-primitive p (eval sv ρ1)) .(eval-primitive p (eval sv ρ2)) .1 (s≤s j<k) (primapp .p .sv) (primapp .p .sv) =
   deval-primitive p (eval sv ρ1) (deval (derive-dsval sv) ρ1 dρ) , dprimapp p sv (derive-dsval sv) ,
     rfundamental3primv k p (eval sv ρ1) (deval (derive-dsval sv) ρ1 dρ) (eval sv ρ2) (rfundamental3svv k sv ρ1 dρ ρ2 ρρ)
-- (eval sv ρ1) (deval (derive-dsval sv) ρ1 dρ) (eval sv ρ2) k
rfundamental3 (suc (suc (suc (suc k)))) (app vs vt) ρ1 dρ ρ2 ρρ v1 v2 .(suc (suc (suc j))) (s≤s (s≤s (s≤s (s≤s j<k))))
  (app j vtv1 ρ1⊢t1↓[j]v1 ρ1⊢t1↓[j]v2 ρ1⊢t1↓[j]v3)
  (app n₁ vtv2 ρ2⊢t2↓[n2]v2 ρ2⊢t2↓[n2]v3 ρ2⊢t2↓[n2]v4)
  with rfundamental3 (suc (suc (suc (suc k)))) (val vs) ρ1 dρ ρ2 ρρ _ _ (suc zero) (s≤s (s≤s z≤n)) ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2
       | rfundamental3 (suc (suc (suc (suc k)))) (val vt) ρ1 dρ ρ2 ρρ _ _ (suc zero) (s≤s (s≤s z≤n)) ρ1⊢t1↓[j]v2 ρ2⊢t2↓[n2]v3
... | bang f2 , vs↓dsv , refl | dtv , vt↓dvv , dtvv
      rewrite sym (rrelρ3→⊕ ρ1 dρ ρ2 ρρ) =
        bang v2 , bangapp vs↓dsv ρ2⊢t2↓[n2]v3 ρ2⊢t2↓[n2]v4 , refl
... | dclosure dt ρ dρ₁ , vs↓dsv , (refl , refl) , refl , refl , refl , refl , dsvv | dtv , vt↓dvv , dtvv
      with dsvv (suc k) (s≤s (s≤s (≤-step ≤-refl))) vtv1 dtv vtv2
           ( (rrelV3-mono (suc k) (suc (suc (suc k))) (s≤s (≤-step (≤-step ≤-refl))) _ vtv1 dtv vtv2 dtvv) )
           v1 v2 j (s≤s j<k) ρ1⊢t1↓[j]v3 ρ2⊢t2↓[n2]v4
... | dv , ↓dv , dvv =
      dv , dapp vs↓dsv ρ1⊢t1↓[j]v2 vt↓dvv ↓dv , dvv
rfundamental3 (suc (suc k)) (lett s t) ρ1 dρ ρ2 ρρ v1 v2 .(suc (n1 + n2)) (s≤s (s≤s n1+n2≤k))
  (lett n1 n2 vs1 .s .t ρ1⊢t1↓[j]v1 ρ1⊢t1↓[j]v2) (lett _ _ vs2 .s .t ρ2⊢t2↓[n2]v2 ρ2⊢t2↓[n2]v3)
  with rfundamental3 (suc (suc k)) s ρ1 dρ ρ2 ρρ vs1 vs2 n1
    (s≤s (≤-trans (≤-trans (m≤m+n n1 n2) n1+n2≤k) (≤-step ≤-refl)))
    ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2
... | dsv , ↓dsv , vsv
      with rfundamental3 (suc (suc k) ∸ n1) t (vs1 • ρ1) (dsv • dρ) (vs2 • ρ2) (vsv , rrelρ3-mono (suc (suc k) ∸ n1) (suc (suc k)) (m∸n≤m (suc (suc k)) n1) _ _ _ _ ρρ) v1 v2 n2 (sub∸ n1 (suc n2) (suc (suc k)) n1+[1+n2]≤2+k) ρ1⊢t1↓[j]v2 ρ2⊢t2↓[n2]v3
      where
        n1+[1+n2]≤2+k : n1 + suc n2 ≤ suc (suc k)
        n1+[1+n2]≤2+k rewrite +-suc n1 n2 = ≤-step (s≤s n1+n2≤k)
... | dv , ↓dv , dvv = dv , dlett ρ1⊢t1↓[j]v1 ↓dsv ↓dv , rrelV3-mono (suc k ∸ (n1 + n2)) (suc (suc k) ∸ n1 ∸ n2) 1+k-[n1+n2]≤2+k-n1-n2 _ v1 dv v2 dvv
  where
    1+k-[n1+n2]≤2+k-n1-n2 : suc k ∸ (n1 + n2) ≤ suc (suc k) ∸ n1 ∸ n2
    1+k-[n1+n2]≤2+k-n1-n2 rewrite ∸-+-assoc (suc (suc k)) n1 n2 = ∸-mono {suc k} {suc (suc k)} {n1 + n2} {n1 + n2} (≤-step ≤-refl) ≤-refl
