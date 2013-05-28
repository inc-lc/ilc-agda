module Denotational.WeakValidChanges where

open import Data.Product
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.ChangeTypes.ChangesAreDerivatives

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Changes
open import Denotational.EqualityLemmas

-- DEFINITION of weakly valid changes via a logical relation

-- Strong validity:
open import Denotational.ValidChanges

-- Weak validity, defined through a function producing a type.
--
-- Since this is a logical relation, this couldn't be defined as a
-- datatype, since it is not strictly positive.

Weak-Valid-Δ : {τ : Type} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧ → Set
Weak-Valid-Δ {bool} v dv = ⊤
Weak-Valid-Δ {S ⇒ T} f df =
  ∀ (s : ⟦ S ⟧) ds (valid-w : Weak-Valid-Δ s ds) →
    Weak-Valid-Δ (f s) (df s ds) ×
    df is-correct-for f on s and ds

strong-to-weak-validity : ∀ {τ : Type} {v : ⟦ τ ⟧} {dv} → Valid-Δ v dv → Weak-Valid-Δ v dv
strong-to-weak-validity {bool} _ = tt
strong-to-weak-validity {τ ⇒ τ₁} {v} {dv} s-valid-v-dv = λ s ds _ → 
  let
    proofs = s-valid-v-dv s ds
    dv-s-ds-valid-on-v-s = proj₁ proofs
    dv-is-correct-for-v-on-s-and-ds = proj₂ proofs
  in
    strong-to-weak-validity dv-s-ds-valid-on-v-s , dv-is-correct-for-v-on-s-and-ds

{-
-- This proof doesn't go through: the desired equivalence is too
-- strong, and we can't fill the holes because dv is arbitrary.

diff-apply-proof-weak : ∀ {τ} (dv : ⟦ Δ-Type τ ⟧) (v : ⟦ τ ⟧) →
    (Weak-Valid-Δ v dv) → diff (apply dv v) v ≡ dv

diff-apply-proof-weak {τ₁ ⇒ τ₂} df f df-valid = ext (λ v → ext (λ dv →
  begin
    diff (apply (df (apply dv v) (derive (apply dv v))) (f (apply dv v))) (f v)
  ≡⟨ ≡-cong
     (λ x → diff x (f v))
       (sym (proj₂ (df-valid (apply dv v) (derive (apply dv v)) (strong-to-weak-validity (derive-is-valid (apply dv v)))))) ⟩
    diff ((apply df f) (apply (derive (apply dv v)) (apply dv v))) (f v)
  ≡⟨ ≡-cong
     (λ x → diff (apply df f x) (f v))
       (apply-derive (apply dv v)) ⟩
    diff ((apply df f) (apply dv v)) (f v)
  ≡⟨ ≡-cong
     (λ x → diff x (f v))
       (proj₂ (df-valid v dv {!!})) ⟩
    diff (apply (df v dv) (f v)) (f v)
  ≡⟨ diff-apply-proof-weak {τ₂} (df v dv) (f v) (proj₁ (df-valid v dv {!!})) ⟩
    df v dv
  ∎)) where open ≡-Reasoning

diff-apply-proof-weak {bool} db b _ = xor-cancellative b db

-- That'd be the core of the proof of diff-apply-weak, if we relax the
-- equivalence in the goal to something more correct. We need a proof
-- of validity only for the first argument, somehow: maybe because
-- diff itself produces strongly valid changes?
--
-- Ahah! Not really: below we use the unprovable
-- diff-apply-proof-weak. To be able to use induction, we need to use
-- this weaker lemma again. Hence, we'll only be able to prove the
-- same equivalence, which will needs another proof of validity to
-- unfold further until the base case.

diff-apply-proof-weak-f : ∀ {τ₁ τ₂} (df : ⟦ Δ-Type (τ₁ ⇒ τ₂) ⟧) (f : ⟦ τ₁ ⇒ τ₂ ⟧) →
    (Weak-Valid-Δ f df) → ∀ dv v → (Weak-Valid-Δ v dv) → (diff (apply df f) f) v dv ≡ df v dv

diff-apply-proof-weak-f {τ₁} {τ₂} df f df-valid dv v dv-valid =
  begin
    diff (apply (df (apply dv v) (derive (apply dv v))) (f (apply dv v))) (f v)
  ≡⟨ ≡-cong
     (λ x → diff x (f v))
       (sym (proj₂ (df-valid (apply dv v) (derive (apply dv v)) (strong-to-weak-validity (derive-is-valid (apply dv v)))))) ⟩
    diff ((apply df f) (apply (derive (apply dv v)) (apply dv v))) (f v)
  ≡⟨ ≡-cong
     (λ x → diff (apply df f x) (f v))
       (apply-derive (apply dv v)) ⟩
    diff ((apply df f) (apply dv v)) (f v)
  ≡⟨ ≡-cong
     (λ x → diff x (f v))
       (proj₂ (df-valid v dv dv-valid)) ⟩
    diff (apply (df v dv) (f v)) (f v)
  ≡⟨ diff-apply-proof-weak {τ₂} (df v dv) (f v) (proj₁ (df-valid v dv dv-valid)) ⟩
    df v dv
  ∎ where open ≡-Reasoning
-}

-- A stronger delta equivalence. Note this isn't a congruence; it
-- should be possible to define some congruence rules, but those will
-- be more complex.

data _≈_ : {τ : Type} → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧ → Set where
  --base : ∀ (v : ⟦ bool ⟧) → v ≈ v
  base : ∀ (v1 v2 : ⟦ bool ⟧) → (≡ : v1 ≡ v2) → v1 ≈ v2
  fun : ∀ {σ τ} (f1 f2 : ⟦ Δ-Type (σ ⇒ τ) ⟧) →
    (t≈ : ∀ s ds (valid : Weak-Valid-Δ s ds) → f1 s ds ≈ f2 s ds) →
    f1 ≈ f2

≡→≈ : ∀ {τ} {v1 v2 : ⟦ Δ-Type τ ⟧} → v1 ≡ v2 → v1 ≈ v2
≡→≈ {bool} {v1} {.v1} refl = base v1 v1 refl
≡→≈ {τ₁ ⇒ τ₂} {v1} {.v1} refl = fun v1 v1 (λ s ds _ → ≡→≈ refl)

open import Relation.Binary hiding (_⇒_)

≈-refl : ∀ {τ} → Reflexive (_≈_ {τ})
≈-refl = ≡→≈ refl

≈-sym : ∀ {τ} → Symmetric (_≈_ {τ})
≈-sym (base v1 v2 ≡) = base _ _ (sym ≡)
≈-sym {(σ ⇒ τ)} (fun f1 f2 t≈) = fun _ _  (λ s ds valid → ≈-sym (t≈ s ds valid))

≈-trans : ∀ {τ} → Transitive (_≈_ {τ})
≈-trans {.bool} {.k} {.k} {k} (base .k .k refl) (base .k .k refl) = base k k refl
≈-trans {σ ⇒ τ} {.f1} {.f2} {k} (fun f1 .f2 ≈₁) (fun f2 .k ≈₂) = fun f1 k (λ s ds valid → ≈-trans (≈₁ _ _ valid) (≈₂ _ _ valid))

≈-isEquivalence : ∀ {τ} → IsEquivalence (_≈_ {τ})
≈-isEquivalence = record
  { refl  = ≈-refl
  ; sym   = ≈-sym
  ; trans = ≈-trans
  }

≈-setoid : Type → Setoid _ _
≈-setoid τ = record
  { Carrier       = ⟦ Δ-Type τ ⟧
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

module ≈-Reasoning where
  module _ {τ : Type} where
    open import Relation.Binary.EqReasoning (≈-setoid τ) public
      hiding (_≡⟨_⟩_)

-- Correct proof, to refactor using ≈-Reasoning

diff-apply-proof-weak-real : ∀ {τ} (dv : ⟦ Δ-Type τ ⟧) (v : ⟦ τ ⟧) →
    (Weak-Valid-Δ v dv) → diff (apply dv v) v ≈ dv
diff-apply-proof-weak-real {τ₁ ⇒ τ₂} df f df-valid = fun _ _ (λ v dv dv-valid → ≈-trans (≡→≈ (
  begin
    diff (apply (df (apply dv v) (derive (apply dv v))) (f (apply dv v))) (f v)
  ≡⟨ ≡-cong
     (λ x → diff x (f v))
       (sym (proj₂ (df-valid (apply dv v) (derive (apply dv v)) (strong-to-weak-validity (derive-is-valid (apply dv v)))))) ⟩
    diff ((apply df f) (apply (derive (apply dv v)) (apply dv v))) (f v)
  ≡⟨ ≡-cong
     (λ x → diff (apply df f x) (f v))
       (apply-derive (apply dv v)) ⟩
    diff ((apply df f) (apply dv v)) (f v)
  ≡⟨ ≡-cong
     (λ x → diff x (f v))
       (proj₂ (df-valid v dv dv-valid)) ⟩
    diff (apply (df v dv) (f v)) (f v)
  ∎)) (diff-apply-proof-weak-real {τ₂} (df v dv) (f v) (proj₁ (df-valid v dv dv-valid))))
  --≈⟨ fill in the above proof ⟩
    --df v dv

  where open ≡-Reasoning

diff-apply-proof-weak-real {bool} db b _ = ≡→≈ (xor-cancellative b db)
