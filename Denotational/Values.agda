module Denotational.Values where

-- VALUES
--
-- This module defines the model theory of simple types, that is,
-- it defines for every type, the set of values of that type.
--
-- In fact, we only describe a single model here.

open import Data.Bool public

import Relation.Binary as B

open import Relation.Binary using
  (IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
import Relation.Binary.EqReasoning as EqR

open import Relation.Nullary using (¬_)

open import Denotational.Notation

open import Syntactic.Types

-- Denotational Semantics

⟦_⟧Type : Type -> Set
⟦ τ₁ ⇒ τ₂ ⟧Type = ⟦ τ₁ ⟧Type → ⟦ τ₂ ⟧Type
⟦ bool ⟧Type = Bool

meaningOfType : Meaning Type
meaningOfType = meaning ⟦_⟧Type

-- Value Equivalence
open import Level using (zero)
open import Relation.Binary.PropositionalEquality
postulate ext : Extensionality zero zero

not-not : ∀ a → a ≡ not (not a)
not-not true = refl
not-not false = refl

a-xor-a-false : ∀ a → (a xor a) ≡ false
a-xor-a-false true = refl
a-xor-a-false false = refl

a-xor-false-a : ∀ a → (false xor a) ≡ a
a-xor-false-a b = refl

xor-associative : ∀ a b c → ((b xor c) xor a) ≡ (b xor (c xor a))
xor-associative a true true = not-not a
xor-associative a true false = refl
xor-associative a false c = refl

a-xor-false : ∀ a → a xor false ≡ a
a-xor-false true = refl
a-xor-false false = refl

a-xor-true : ∀ a → a xor true ≡ not a
a-xor-true true = refl
a-xor-true false = refl

xor-commutative : ∀ a b → a xor b ≡ b xor a
xor-commutative true b rewrite a-xor-true b = refl
xor-commutative false b rewrite a-xor-false b = refl

xor-cancellative-2 : ∀ a b → (b xor (a xor a)) ≡ b
xor-cancellative-2 a b rewrite a-xor-a-false a = a-xor-false b

xor-cancellative : ∀ a b → ((b xor a) xor a) ≡ b
xor-cancellative a b rewrite xor-associative a b a = xor-cancellative-2 a b

≡-refl : ∀ {τ} {v : ⟦ τ ⟧} →
  v ≡ v
≡-refl = refl

≡-sym : ∀ {τ} {v₁ v₂ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₂ ≡ v₁
≡-sym = sym

≡-trans : ∀ {τ} {v₁ v₂ v₃ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₂ ≡ v₃ → v₁ ≡ v₃
≡-trans = trans

≡-cong : ∀ {τ₂ τ₁ v₁ v₂} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧) →
  v₁ ≡ v₂ → f v₁ ≡ f v₂
≡-cong f = cong f
≡-cong₂ : ∀ {τ₃ τ₁ τ₂ v₁ v₂ v₃ v₄} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ₃ ⟧) →
  v₁ ≡ v₂ → v₃ ≡ v₄ → f v₁ v₃ ≡ f v₂ v₄
≡-cong₂ f = cong₂ f

≡-app : ∀ {τ₁ τ₂} {v₁ v₂ : ⟦ τ₁ ⇒ τ₂ ⟧} {v₃ v₄ : ⟦ τ₁ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → v₁ v₃ ≡ v₂ v₄
≡-app = ≡-cong₂ (λ x y → x y)

≡-if_then_else_ : ∀ {τ} {v₁ v₂ : ⟦ bool ⟧} {v₃ v₄ v₅ v₆ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → v₅ ≡ v₆ →
  (if v₁ then v₃ else v₅) ≡ (if v₂ then v₄ else v₆)
≡-if refl then refl else refl = refl

≡-isEquivalence : ∀ {τ : Set} → IsEquivalence (_≡_ {A = τ})
≡-isEquivalence = isEquivalence

≡-setoid : Type → Setoid _ _
≡-setoid τ = record
  { Carrier       = ⟦ τ ⟧
  ; _≈_           = _≡_
  ; isEquivalence = ≡-isEquivalence
  }

≡-consistent : ¬ (∀ (τ : Type) → (v₁ v₂ : ⟦ τ ⟧) → v₁ ≡ v₂)
≡-consistent H with H bool true false
... | ()
