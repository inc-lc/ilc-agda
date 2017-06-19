--
-- In this module we conclude our proof: we have shown that t, derive-dterm t
-- and produce related values (in the sense of the fundamental property,
-- rfundamental3), and for related values v1, dv and v2 we have v1 ⊕ dv ≡
-- v2 (because ⊕ agrees with validity, rrelV3→⊕).
--
-- We now put these facts together via derive-correct-si and derive-correct.
-- This is immediate, even though I spend so much code on it:
-- Indeed, all theorems are immediate corollaries of what we established (as
-- explained above); only the statements are longer, especially because I bother
-- expanding them.

module Thesis.SIRelBigStep.DeriveCorrect where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Thesis.SIRelBigStep.IlcSILR
open import Thesis.SIRelBigStep.FundamentalProperty

-- Theorem statement. This theorem still mentions step-indexes explicitly.
derive-correct-si-type =
  ∀ {τ Γ k} (t : Term Γ τ) ρ1 dρ ρ2 → (ρρ : rrelρ3 Γ ρ1 dρ ρ2 k) →
  rrelT3-skeleton (λ v1 dv v2 _ → v1 ⊕ dv ≡ v2) t (derive-dterm t) t ρ1 dρ ρ2 k

-- A verified expansion of the theorem statement.
derive-correct-si-type-means :
  derive-correct-si-type ≡
  ∀ {τ Γ k} (t : Term Γ τ)
  ρ1 dρ ρ2 (ρρ : rrelρ3 Γ ρ1 dρ ρ2 k) →
  (v1 v2 : Val τ) →
  ∀ j (j<k : j < k) →
  (ρ1⊢t1↓[j]v1 : ρ1 ⊢ t ↓[ i' j ] v1) →
  (ρ2⊢t2↓[n2]v2 : ρ2 ⊢ t ↓[ no ] v2) →
  Σ[ dv ∈ DVal τ ]
  ρ1 D dρ ⊢ derive-dterm t ↓ dv ×
  v1 ⊕ dv ≡ v2
derive-correct-si-type-means = refl

derive-correct-si : derive-correct-si-type
derive-correct-si t ρ1 dρ ρ2 ρρ = rrelT3→⊕ t (derive-dterm t) t ρ1 dρ ρ2 (rfundamental3 _ t ρ1 dρ ρ2 ρρ)

-- Infinitely related environments:
rrelρ3-inf : ∀ Γ (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → Set
rrelρ3-inf Γ ρ1 dρ ρ2 = ∀ k → rrelρ3 Γ ρ1 dρ ρ2 k

-- A theorem statement for infinitely-related environments. On paper, if we informally
-- omit the arbitrary derivation step-index as usual, we get a statement without
-- step-indexes.
derive-correct :
  ∀ {τ Γ} (t : Term Γ τ)
  ρ1 dρ ρ2 (ρρ : rrelρ3-inf Γ ρ1 dρ ρ2) →
  (v1 v2 : Val τ) →
  ∀ j →
  (ρ1⊢t1↓[j]v1 : ρ1 ⊢ t ↓[ i' j ] v1) →
  (ρ2⊢t2↓[n2]v2 : ρ2 ⊢ t ↓[ no ] v2) →
  Σ[ dv ∈ DVal τ ]
  ρ1 D dρ ⊢ derive-dterm t ↓ dv ×
  v1 ⊕ dv ≡ v2
derive-correct t ρ1 dρ ρ2 ρρ v1 v2 j = derive-correct-si t ρ1 dρ ρ2 (ρρ (suc j)) v1 v2 j ≤-refl

open import Data.Unit

nilρ : ∀ {Γ n} (ρ : ⟦ Γ ⟧Context) → Σ[ dρ ∈ ChΔ Γ ] rrelρ3 Γ ρ dρ ρ n
nilV : ∀ {τ n} (v : Val τ) → Σ[ dv ∈ DVal τ ] rrelV3 τ v dv v n
nilV (closure t ρ) = let dρ , ρρ = nilρ ρ in dclosure (derive-dterm t) ρ dρ , rfundamental3svv _ (abs t) ρ dρ ρ ρρ
nilV (natV n₁) = dnatV zero , refl
nilV (pairV a b) = let 0a , aa = nilV a; 0b , bb = nilV b in dpairV 0a 0b , aa , bb

nilρ ∅ = ∅ , tt
nilρ (v • ρ) = let dv , vv = nilV v ; dρ , ρρ = nilρ ρ in dv • dρ , vv , ρρ

-- Try to prove to define validity-preserving change composition.
-- Sadly, if we don't store proofs that environment changes in closures are valid, we can't finish the proof for the closure case :-(.
-- Moreover, the proof is annoying to do unless we build a datatype to invert
-- validity proofs (as suggested by Ezyang in
-- http://blog.ezyang.com/2013/09/induction-and-logical-relations/).

-- ocomposeρ : ∀ {Γ} n ρ1 dρ1 ρ2 dρ2 ρ3 → rrelρ3 Γ ρ1 dρ1 ρ2 n → rrelρ3 Γ ρ2 dρ2 ρ3 n → Σ[ dρ ∈ ChΔ Γ ] rrelρ3 Γ ρ1 dρ ρ3 n

-- ocomposev : ∀ {τ} n v1 dv1 v2 dv2 v3 → rrelV3 τ v1 dv1 v2 n → rrelV3 τ v2 dv2 v3 n → Σ[ dv ∈ DVal τ ] rrelV3 τ v1 dv v3 n
-- ocomposev n v1 dv1 v2 (bang v3) .v3 vv1 refl = bang v3 , refl
-- ocomposev n v1 (bang x) v2 (dclosure dt ρ dρ) v3 vv1 vv2 = {!!}
-- ocomposev n (closure t ρ) (dclosure .(derive-dterm t) .ρ dρ1) (closure .t .(ρ ⊕ρ dρ1)) (dclosure .(derive-dterm t) .(ρ ⊕ρ dρ1) dρ2) (closure .t .((ρ ⊕ρ dρ1) ⊕ρ dρ2)) ((refl , refl) , refl , refl , refl , refl , p5) ((refl , refl) , refl , refl , refl , refl , p5q) =
--   let dρ , ρρ = ocomposeρ n ρ dρ1 (ρ ⊕ρ dρ1) dρ2 ((ρ ⊕ρ dρ1) ⊕ρ dρ2) {!!} {!!}
--   in dclosure (derive-dterm t) ρ dρ , (refl , refl) , refl , {!!} , refl , refl ,
--     λ { k (s≤s k<n) v1 dv v2 vv →
--       rfundamental3 k t (v1 • ρ) (dv • dρ) (v2 • ((ρ ⊕ρ dρ1) ⊕ρ dρ2)) (vv , rrelρ3-mono k n (≤-step k<n) _ ρ dρ ((ρ ⊕ρ dρ1) ⊕ρ dρ2) ρρ)}
-- -- p1 , p2 , p3 , p4 , p5
-- ocomposev n v1 dv1 v2 (dnatV n₁) v3 vv1 vv2 = {!!}
-- ocomposev n v1 dv1 v2 (dpairV dv2 dv3) v3 vv1 vv2 = {!!}
-- -- ocomposev n v1 (bang v2) .v2 dv2 v3 refl vv2 = bang (v2 ⊕ dv2) , rrelV3→⊕ v2 dv2 v3 vv2
-- -- ocomposev n v1 (dclosure dt ρ dρ) v2 dv2 v3 vv1 vv2 = {!!}
-- -- ocomposev n v1 (dnatV n₁) v2 dv2 v3 vv1 vv2 = {!!}
-- -- ocomposev n v1 (dpairV dv1 dv2) v2 dv3 v3 vv1 vv2 = {!!}
-- -- ocomposeV : ∀ {τ n} (v : Val τ) → Σ[ dv ∈ DVal τ ] rrelV3 τ v dv v n

-- ocomposeρ {∅} n ∅ dρ1 ρ2 dρ2 ∅ ρρ1 ρρ2 = ∅ , tt
-- ocomposeρ {τ • Γ} n (v1 • ρ1) (dv1 • dρ1) (v2 • ρ2) (dv2 • dρ2) (v3 • ρ3) (vv1 , ρρ1) (vv2 , ρρ2) =
--   let dv , vv = ocomposev n v1 dv1 v2 dv2 v3 vv1 vv2
--       dρ , ρρ = ocomposeρ n ρ1 dρ1 ρ2 dρ2 ρ3 ρρ1 ρρ2
--   in  dv • dρ , vv , ρρ

-- But we sort of know how to store environments validity proofs in closures, you just need to use well-founded inductions, even if you're using types. Sad, yes, that's insanely tedious. Let's leave that to Coq.
-- What is also interesting: if that were fixed, could we prove correct
-- composition for change *terms* and rrelT3? And for *open expressions*? The
-- last is the main problem Ahmed run into.
