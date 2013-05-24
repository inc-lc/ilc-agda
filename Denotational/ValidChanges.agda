module Denotational.ValidChanges where

open import Data.Product
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Syntactic.Types

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Equivalence

open import Changes

-- DEFINITION of valid changes via a logical relation

{-
What I wanted to write:

data Valid-Δ : {T : Type} → (v : ⟦ T ⟧) → (dv : ⟦ Δ-Type T ⟧) → Set where
  base : (v : ⟦ bool ⟧) → (dv : ⟦ Δ-Type bool ⟧) → ValidΔ v dv
  fun : ∀ {S T} → (f : ⟦ S ⇒ T ⟧) → (df : ⟦ Δ-Type (S ⇒ T) ⟧) →
    (∀ (s : ⟦ S ⟧) ds → (ValidΔ (f s) (df s ds)) × ((apply df f) (apply ds s) ≡ apply (df s ds) (f s))) → 
    ValidΔ f df
-}

-- What I had to write:
-- Note: now I could go back to using a datatype, since the datatype is now strictly positive.
Valid-Δ : {τ : Type} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧ → Set
Valid-Δ {bool} v dv = ⊤
Valid-Δ {S ⇒ T} f df =
  ∀ (s : ⟦ S ⟧) ds {- (valid-w : Valid-Δ s ds) -} →
    Valid-Δ (f s) (df s ds) ×
    (apply df f) (apply ds s) ≡ apply (df s ds) (f s)

invalid-changes-exist : ¬ (∀ {τ} v dv → Valid-Δ {τ} v dv)
invalid-changes-exist k with k (λ x → x) (λ x dx → false) false true
... | _ , ()

diff-is-valid : ∀ {τ} (v′ v : ⟦ τ ⟧) → Valid-Δ {τ} v (diff v′ v)
diff-is-valid {bool} v′ v = tt
diff-is-valid {τ ⇒ τ₁} v′ v =
  λ s ds →
    diff-is-valid (v′ (apply ds s)) (v s) , (
    begin
      apply (diff v′ v) v (apply ds s)
    ≡⟨ refl ⟩
      apply
        (diff (v′ (apply (derive (apply ds s)) (apply ds s))) (v (apply ds s)))
        (v (apply ds s))
    ≡⟨ ≡-cong (λ x → apply (diff (v′ x) (v (apply ds s))) (v (apply ds s))) (apply-derive (apply ds s)) ⟩
      apply (diff (v′ (apply ds s)) (v (apply ds s))) (v (apply ds s))
    ≡⟨ apply-diff (v (apply ds s)) (v′ (apply ds s)) ⟩
      v′ (apply ds s)
    ≡⟨ sym (apply-diff (v s) (v′ (apply ds s))) ⟩
      apply ((diff v′ v) s ds) (v s)
    ∎) where open ≡-Reasoning

derive-is-valid : ∀ {τ} (v : ⟦ τ ⟧) → Valid-Δ {τ} v (derive v)
derive-is-valid v rewrite sym (diff-derive v) = diff-is-valid v v

-- This is a postulate elsewhere, but here I provide a proper proof.

diff-apply-proof : ∀ {τ} (dv : ⟦ Δ-Type τ ⟧) (v : ⟦ τ ⟧) →
    (Valid-Δ v dv) → diff (apply dv v) v ≡ dv

diff-apply-proof {τ₁ ⇒ τ₂} df f df-valid = ext (λ v → ext (λ dv →
  begin
    diff (apply (df (apply dv v) (derive (apply dv v))) (f (apply dv v))) (f v)
  ≡⟨ ≡-cong
     (λ x → diff x (f v))
       (sym (proj₂ (df-valid (apply dv v) (derive (apply dv v))))) ⟩
    diff ((apply df f) (apply (derive (apply dv v)) (apply dv v))) (f v)
  ≡⟨ ≡-cong
     (λ x → diff (apply df f x) (f v))
       (apply-derive (apply dv v)) ⟩
    diff ((apply df f) (apply dv v)) (f v)
  ≡⟨ ≡-cong
     (λ x → diff x (f v))
       (proj₂ (df-valid v dv)) ⟩
    diff (apply (df v dv) (f v)) (f v)
  ≡⟨ diff-apply-proof {τ₂} (df v dv) (f v) (proj₁ (df-valid v dv)) ⟩
    df v dv
  ∎)) where open ≡-Reasoning

diff-apply-proof {bool} db b _ = xor-cancellative b db

open import Syntactic.Contexts Type
open import Denotational.Environments Type ⟦_⟧Type
open import Changes
open import ChangeContexts

ProofVal : Type → Set
ProofVal τ = Σ[ v ∈ ⟦ τ ⟧ ] (Σ[ dv ∈ ⟦ Δ-Type τ ⟧ ] Valid-Δ v dv)

import Denotational.Environments Type ProofVal as ProofEnv

eraseVal : ∀ {τ} → ProofVal τ → ⟦ τ ⟧
eraseVal (v , dv , dv-valid) = v

-- Specification: eraseEnv = map eraseVal
eraseEnv : ∀ {Γ} → ProofEnv.⟦ Γ ⟧Context → ⟦ Γ ⟧
eraseEnv {∅} ∅ = ∅
eraseEnv {τ • Γ} (v • ρ) = eraseVal v • eraseEnv ρ

eraseProofs : ∀ {Γ} → ProofEnv.⟦ Γ ⟧Context → ⟦ Δ-Context Γ ⟧
eraseProofs {∅} ∅ = ∅
eraseProofs {τ • Γ} ((v , dv , dv-valid) • ρ) = dv • v • eraseProofs ρ
