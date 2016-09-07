module Base.HetEqExtra where

open import Relation.Binary.HeterogeneousEquality

-- More dependent variant of subst₂ from Relation.Binary.HeterogeneousEquality, see e.g.
-- http://stackoverflow.com/a/24255198/53974
hsubst₂ : ∀ {a b p} {A : Set a} {B : A → Set b} (P : (a : A) → (B a) → Set p) →
         ∀ {x₁ x₂ y₁ y₂} → x₁ ≅ x₂ → y₁ ≅ y₂ → P x₁ y₁ → P x₂ y₂
hsubst₂ P refl refl p = p

-- subst-removable for hsubst₂
hsubst₂-removable : ∀ {a b p} {A : Set a} {B : A → Set b} (P : (a : A) → (B a) → Set p) →
         ∀ {x₁ x₂ y₁ y₂} (≅₁ : x₁ ≅ x₂) (≅₂ : y₁ ≅ y₂) p → hsubst₂ P ≅₁ ≅₂ p ≅ p
hsubst₂-removable P refl refl p = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x y → C x y → Set d}
        {x y u v z w}
        (f : (x : A) (y : B x) → (z : C x y) → D x y z) → x ≅ y → u ≅ v → z ≅ w → f x u z ≅ f y v w
cong₃ f refl refl refl = refl
