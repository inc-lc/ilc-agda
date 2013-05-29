module Denotational.Changes where

-- CHANGES
--
-- This module defines the representation of changes, the
-- available operations on changes, and properties of these
-- operations.

open import Syntactic.Types
open import Syntactic.ChangeTypes.ChangesAreDerivatives

open import Denotational.Notation
open import Denotational.Values

open import Denotational.EqualityLemmas

derive : ∀ {τ} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧
apply : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ⟦ τ ⟧ → ⟦ τ ⟧
diff : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧

diff {τ₁ ⇒ τ₂} f₁ f₂ = λ v dv → diff (f₁ (apply dv v)) (f₂ v)
diff {bool} b c = b xor c

derive {τ₁ ⇒ τ₂} f = λ v dv → diff (f (apply dv v)) (f v)
derive {bool} b = false

apply {τ₁ ⇒ τ₂} df f = λ v → apply (df v (derive v)) (f v)
apply {bool} b c = b xor c

compose : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧
compose {τ₁ ⇒ τ₂} df₁ df₂ = λ v dv → compose (df₁ v dv) (df₂ v dv)
compose {bool} b c = b xor c

-- CONGRUENCE rules for change operations

open import Relation.Binary.PropositionalEquality

≡-diff : ∀ {τ : Type} {v₁ v₂ v₃ v₄ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → diff v₁ v₃ ≡ diff v₂ v₄
≡-diff = ≡-cong₂ diff

≡-apply : ∀ {τ : Type} {dv₁ dv₂ : ⟦ Δ-Type τ ⟧} {v₁ v₂ : ⟦ τ ⟧} →
  dv₁ ≡ dv₂ → v₁ ≡ v₂ → apply dv₁ v₁ ≡ apply dv₂ v₂
≡-apply = ≡-cong₂ apply

-- PROPERTIES of changes

diff-derive : ∀ {τ} (v : ⟦ τ ⟧) →
  diff v v ≡ derive v
diff-derive {τ₁ ⇒ τ₂} v = ≡-refl

diff-derive {bool} b = a-xor-a-false b

-- Here used to live diff-apply, which turned out to be incorrect. For
-- a correct version, see diff-apply-proof in
-- Denotational.ValidChanges
{-
-- false:
postulate
  diff-apply : ∀ {τ} (dv : ⟦ Δ-Type τ ⟧) (v : ⟦ τ ⟧) →
    diff (apply dv v) v ≡ dv
-}

apply-diff : ∀ {τ} (v₁ v₂ : ⟦ τ ⟧) →
  apply (diff v₂ v₁) v₁ ≡ v₂

apply-derive : ∀ {τ} (v : ⟦ τ ⟧) →
  apply (derive v) v ≡ v

apply-diff {τ₁ ⇒ τ₂} f₁ f₂ = ext (λ v →
  begin
    apply (diff f₂ f₁) f₁ v
  ≡⟨ ≡-refl ⟩
    apply (diff (f₂ (apply (derive v) v)) (f₁ v)) (f₁ v)
  ≡⟨ ≡-apply (≡-diff (≡-cong f₂ (apply-derive v)) ≡-refl) ≡-refl ⟩
    apply (diff (f₂ v) (f₁ v)) (f₁ v)
  ≡⟨ apply-diff (f₁ v) (f₂ v) ⟩
    f₂ v
  ∎) where open ≡-Reasoning
apply-diff {bool} a b = xor-cancellative a b

apply-derive {τ₁ ⇒ τ₂} f = ext (λ v →
  begin
    apply (derive f) f v
  ≡⟨ ≡-refl ⟩
    apply (diff (f (apply (derive v) v)) (f v)) (f v)
  ≡⟨ ≡-cong (λ x → apply (diff (f x) (f v)) (f v)) (apply-derive v) ⟩
    apply (diff (f v) (f v)) (f v)
  ≡⟨ apply-diff (f v) (f v)⟩
    f v
  ∎) where open ≡-Reasoning
apply-derive {bool} a = a-xor-false-a a

apply-compose : ∀ {τ} (v : ⟦ τ ⟧) (dv₁ dv₂ : ⟦ Δ-Type τ ⟧) →
  apply (compose dv₁ dv₂) v ≡ apply dv₁ (apply dv₂ v)
apply-compose {τ₁ ⇒ τ₂} f df₁ df₂ = ext (λ v →
  apply-compose (f v) (df₁ v (derive v)) (df₂ v (derive v)))
apply-compose {bool} a b c = xor-associative a b c

compose-assoc : ∀ {τ} (dv₁ dv₂ dv₃ : ⟦ Δ-Type τ ⟧) →
  compose dv₁ (compose dv₂ dv₃) ≡ compose (compose dv₁ dv₂) dv₃
compose-assoc {τ₁ ⇒ τ₂} df₁ df₂ df₃ = ext (λ v → ext (λ dv →
  compose-assoc (df₁ v dv) (df₂ v dv) (df₃ v dv)))
compose-assoc {bool} a b c = ≡-sym (xor-associative c a b)
