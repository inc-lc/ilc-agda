-- Utilities for decidable equality

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module experimental.DecidableEq (T : Set) (_≟_ : Decidable {A = T} _≡_) where

open import Data.Empty
open import Data.Bool using (true; false)
open import Relation.Nullary
open import Relation.Nullary.Decidable

≡→≟true : ∀ {v₁ v₂ : T} → (eq : v₁ ≡ v₂) → (v₁ ≟ v₂) ≡ (yes eq)
≡→≟true {v₁} {v₂} eq with v₁ ≟ v₂
≡→≟true {v₁} {.v₁} eq | yes refl = cong yes (proof-irrelevance refl eq)
≡→≟true {v₁} {v₂} eq | no ¬p = ⊥-elim (¬p eq)

≢→≟false : ∀ {v₁ v₂ : T} → (≢ : (v₁ ≡ v₂) → ⊥) → ⌊ v₁ ≟ v₂ ⌋ ≡ false
≢→≟false {v₁} {v₂} ≢ with v₁ ≟ v₂ 
≢→≟false ≢ | yes p = ⊥-elim (≢ p)
≢→≟false ≢ | no ¬p = refl

v≟v-true : ∀ (v : T) → ⌊ (v ≟ v) ⌋ ≡ true
v≟v-true v = cong (λ x → ⌊ x ⌋) (≡→≟true refl)
