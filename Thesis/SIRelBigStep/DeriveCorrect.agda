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
