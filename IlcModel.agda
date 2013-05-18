module IlcModel where

import Relation.Binary as B

open import Relation.Binary using
  (IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
import Relation.Binary.EqReasoning as EqR

open import Relation.Nullary using (¬_)

open import meaning


-- SIMPLE TYPES

-- Syntax

data Type : Set where
  _⇒_ : (τ₁ τ₂ : Type) → Type
  bool : Type

infixr 5 _⇒_

-- Denotational Semantics

data Bool : Set where
  true false : Bool

_xor_ : Bool → Bool → Bool
true xor true = false
true xor false = true
false xor true = true
false xor false = false

not : Bool → Bool
not true = false
not false = false

⟦_⟧Type : Type -> Set
⟦ τ₁ ⇒ τ₂ ⟧Type = ⟦ τ₁ ⟧Type → ⟦ τ₂ ⟧Type
⟦ bool ⟧Type = Bool

meaningOfType : Meaning Type
meaningOfType = meaning ⟦_⟧Type

-- Value Equivalence

data _≡_ : ∀ {τ} → (v₁ v₂ : ⟦ τ ⟧) → Set where
  ext : ∀ {τ₁ τ₂} {f₁ f₂ : ⟦ τ₁ ⇒ τ₂ ⟧} →
    (∀ v → f₁ v ≡ f₂ v) →
    f₁ ≡ f₂
  bool : ∀ {b : Bool} →
    b ≡ b

a-xor-a-false : ∀ a → (a xor a) ≡ false
a-xor-a-false true = bool
a-xor-a-false false = bool

a-xor-false-a : ∀ a → (false xor a) ≡ a
a-xor-false-a true = bool
a-xor-false-a false = bool

xor-cancellative : ∀ a b → ((b xor a) xor a) ≡ b
xor-cancellative true true = bool
xor-cancellative true false = bool
xor-cancellative false true = bool
xor-cancellative false false = bool

xor-associative : ∀ a b c → ((b xor c) xor a) ≡ (b xor (c xor a))

xor-associative true true true = bool
xor-associative true true false = bool
xor-associative true false true = bool
xor-associative true false false = bool
xor-associative false true true = bool
xor-associative false true false = bool
xor-associative false false true = bool
xor-associative false false false = bool

≡-refl : ∀ {τ} {v : ⟦ τ ⟧} →
  v ≡ v
≡-refl {τ₁ ⇒ τ₂} = ext (λ v → ≡-refl)
≡-refl {bool} = bool

≡-sym : ∀ {τ} {v₁ v₂ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₂ ≡ v₁
≡-sym {τ₁ ⇒ τ₂} (ext ≡) = ext (λ v → ≡-sym (≡ v))
≡-sym {bool} bool = bool

≡-trans : ∀ {τ} {v₁ v₂ v₃ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₂ ≡ v₃ → v₁ ≡ v₃
≡-trans {τ₁ ⇒ τ₂} {f} (ext ≡₁) (ext ≡₂) =
  ext (λ v → ≡-trans (≡₁ v) (≡₂ v))
≡-trans {bool} bool bool = bool

postulate
  ≡-cong : ∀ {τ₂ τ₁ v₁ v₂} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧) →
    v₁ ≡ v₂ → f v₁ ≡ f v₂
  ≡-cong₂ : ∀ {τ₃ τ₁ τ₂ v₁ v₂ v₃ v₄} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ₃ ⟧) →
    v₁ ≡ v₂ → v₃ ≡ v₄ → f v₁ v₃ ≡ f v₂ v₄
{-
≡-cong : ∀ {τ₂ τ₁ v₁ v₂} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧) →
  v₁ ≡ v₂ → f v₁ ≡ f v₂
≡-cong {τ₁ ⇒ τ₂} f ≡ = ext (λ v → ≡-cong (λ x → f x v) ≡)
--≡-cong {bool} {bool} {v₁} f bool = bool
≡-cong {bool} {bool} f bool = bool
≡-cong {bool} {τ₃ ⇒ τ₄} {v₁} {v₂} f (ext ≡₁) = {!!}

≡-cong₂ : ∀ {τ₃ τ₁ τ₂ v₁ v₂ v₃ v₄} (f : ⟦ τ₁ ⟧ → ⟦ τ₂ ⟧ → ⟦ τ₃ ⟧) →
  v₁ ≡ v₂ → v₃ ≡ v₄ → f v₁ v₃ ≡ f v₂ v₄
≡-cong₂ {τ₁ ⇒ τ₂} f ≡₁ ≡₂ = ext (λ v → ≡-cong₂ (λ x y → f x y v) ≡₁ ≡₂)
≡-cong₂ {bool} {bool} {bool} f bool bool = bool
≡-cong₂ {bool} {bool} {τ₂ ⇒ τ₃} f bool (ext ≡₂) = {!!}
≡-cong₂ {bool} {τ₁ ⇒ τ₂} {bool} f (ext ≡₁) (bool) = {!!}
≡-cong₂ {bool} {τ₁ ⇒ τ₂} {τ₃ ⇒ τ₄} f (ext ≡₁) (ext ≡₂) = {!!}
-}

≡-app : ∀ {τ₁ τ₂} {v₁ v₂ : ⟦ τ₁ ⇒ τ₂ ⟧} {v₃ v₄ : ⟦ τ₁ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → v₁ v₃ ≡ v₂ v₄
≡-app = ≡-cong₂ (λ x y → x y)

≡-isEquivalence : ∀ {τ} → IsEquivalence (_≡_ {τ})
≡-isEquivalence = record
  { refl  = ≡-refl
  ; sym   = ≡-sym
  ; trans = ≡-trans
  }

≡-setoid : Type → Setoid _ _
≡-setoid τ = record
  { Carrier       = ⟦ τ ⟧
  ; _≈_           = _≡_
  ; isEquivalence = ≡-isEquivalence
  }

module ≡-Reasoning where
  module _ {τ : Type} where
    open EqR (≡-setoid τ) public
      hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _≡⟨_⟩_)

≡-consistent : ¬ (∀ (τ : Type) → (v₁ v₂ : ⟦ τ ⟧) → v₁ ≡ v₂)
≡-consistent H with H bool true false
... | ()
